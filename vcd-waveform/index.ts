import { Type } from "typebox";
import type { ExtensionAPI, ExtensionCommandContext } from "@mariozechner/pi-coding-agent";
import { matchesKey, truncateToWidth } from "@mariozechner/pi-tui";
import { constants as fsConstants } from "node:fs";
import { access, mkdtemp, opendir, readFile, rm } from "node:fs/promises";
import { basename, extname, isAbsolute, join, resolve } from "node:path";
import { tmpdir } from "node:os";
import { execFile } from "node:child_process";
import { promisify } from "node:util";

const execFileAsync = promisify(execFile);

const DEFAULT_TRACE_NAMES = ["dump.vcd", "dump.fst", "waves.vcd", "waves.fst", "wave.vcd", "wave.fst", "trace.vcd", "trace.fst"];
const DEFAULT_VISIBLE_ITEMS = 4;
const DEFAULT_WINDOW = 256;

interface VcdSignal {
  code: string;
  scope: string[];
  name: string;
  width: number;
  kind: string;
  times: number[];
  values: string[];
}

interface VcdTrace {
  path: string;
  timescale: string;
  signals: VcdSignal[];
  maxTime: number;
}

interface TraceSource {
  path: string;
  originalPath: string;
  displayName: string;
  cleanup?: () => Promise<void>;
}

interface VcdToolParams {
  path?: string;
  match?: string;
}

interface ParsedArgs {
  path?: string;
  match?: string;
}

interface TreeScopeNode {
  kind: "scope";
  key: string;
  name: string;
  path: string[];
  depth: number;
  children: TreeNode[];
}

interface TreeSignalNode {
  kind: "signal";
  key: string;
  signal: VcdSignal;
  depth: number;
}

type TreeNode = TreeScopeNode | TreeSignalNode;

interface VisibleScopeItem {
  kind: "scope";
  key: string;
  depth: number;
  node: TreeScopeNode;
}

interface VisibleSignalItem {
  kind: "signal";
  key: string;
  depth: number;
  node: TreeSignalNode;
}

type VisibleItem = VisibleScopeItem | VisibleSignalItem;

function normalizeUserPath(pathText: string): string {
  return pathText.startsWith("@") ? pathText.slice(1) : pathText;
}

function tokenizeArgs(input: string): string[] {
  const tokens: string[] = [];
  let current = "";
  let quote: string | null = null;

  for (let i = 0; i < input.length; i++) {
    const ch = input[i]!;
    if (quote) {
      if (ch === quote) {
        quote = null;
      } else if (ch === "\\" && i + 1 < input.length) {
        current += input[++i]!;
      } else {
        current += ch;
      }
      continue;
    }

    if (ch === '"' || ch === "'") {
      quote = ch;
      continue;
    }

    if (/\s/.test(ch)) {
      if (current) {
        tokens.push(current);
        current = "";
      }
      continue;
    }

    current += ch;
  }

  if (current) tokens.push(current);
  return tokens;
}

function parseCommandArgs(args: string): ParsedArgs {
  const tokens = tokenizeArgs(args.trim());
  const parsed: ParsedArgs = {};

  for (let i = 0; i < tokens.length; i++) {
    const token = tokens[i]!;
    if (token === "--match" && i + 1 < tokens.length) {
      parsed.match = tokens[++i]!;
      continue;
    }
    if (token.startsWith("--match=")) {
      parsed.match = token.slice("--match=".length);
      continue;
    }
    if (token === "--path" && i + 1 < tokens.length) {
      parsed.path = tokens[++i]!;
      continue;
    }
    if (token.startsWith("--path=")) {
      parsed.path = token.slice("--path=".length);
      continue;
    }
    if (!parsed.path) parsed.path = token;
  }

  return parsed;
}

function compileRegex(pattern?: string): RegExp | undefined {
  if (!pattern) return undefined;
  try {
    return new RegExp(pattern);
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    throw new Error(`Invalid match regex: ${message}`);
  }
}

function clip(text: string, width: number): string {
  if (width <= 0) return "";
  if (text.length <= width) return text;
  if (width <= 1) return text.slice(0, 1);
  return `${text.slice(0, width - 1)}…`;
}

function pad(text: string, width: number): string {
  const clipped = clip(text, width);
  return clipped + " ".repeat(Math.max(0, width - clipped.length));
}

function fullName(signal: VcdSignal): string {
  return [...signal.scope, signal.name].join(".");
}

function scopeKey(path: string[]): string {
  return path.join("\u0000");
}

function signalKey(signal: VcdSignal): string {
  return `${scopeKey(signal.scope)}\u0000${signal.name}\u0000${signal.code}`;
}

function unknownValue(width: number): string {
  return width <= 1 ? "x" : "x".repeat(width);
}

function formatValue(signal: VcdSignal, raw: string): string {
  if (signal.width <= 1) {
    return raw[0] ?? "x";
  }

  if (!raw || /[xz]/i.test(raw)) {
    return unknownValue(signal.width);
  }

  if (/^[01]+$/.test(raw)) {
    const digits = Math.max(1, Math.ceil(signal.width / 4));
    const hex = BigInt(`0b${raw}`).toString(16);
    return `0x${hex.padStart(digits, "0")}`;
  }

  return raw;
}

function resolveSignalValue(signal: VcdSignal, time: number): string {
  if (signal.times.length === 0) return unknownValue(signal.width);

  let lo = 0;
  let hi = signal.times.length - 1;
  let idx = -1;

  while (lo <= hi) {
    const mid = (lo + hi) >> 1;
    if (signal.times[mid]! <= time) {
      idx = mid;
      lo = mid + 1;
    } else {
      hi = mid - 1;
    }
  }

  return idx >= 0 ? signal.values[idx]! : unknownValue(signal.width);
}

function signalAtTime(signal: VcdSignal, time: number): string {
  return resolveSignalValue(signal, time);
}

function sampleWaveBlock(signal: VcdSignal, startTime: number, endTime: number, width: number): string[] {
  if (width <= 0) return ["", "", ""];
  const span = Math.max(1, endTime - startTime);
  const top: string[] = [];
  const mid: string[] = [];
  const bottom: string[] = [];
  let previousValue = "";

  for (let col = 0; col < width; col++) {
    const time = width === 1 ? startTime : Math.round(startTime + span * (col / (width - 1)));
    const value = signalAtTime(signal, time);
    const changed = col > 0 && value !== previousValue;

    if (signal.width <= 1) {
      switch (value[0]) {
        case "1":
          top.push("-");
          mid.push(changed ? "│" : " ");
          bottom.push(" ");
          break;
        case "0":
          top.push(" ");
          mid.push(changed ? "│" : " ");
          bottom.push("_");
          break;
        case "x":
        case "z":
          top.push(" ");
          mid.push(value[0]!);
          bottom.push(" ");
          break;
        default:
          top.push(" ");
          mid.push("?");
          bottom.push(" ");
          break;
      }
    } else {
      const isUnknown = /[xz]/i.test(value);
      top.push(col === 0 ? (isUnknown ? "x" : "=") : changed ? "┬" : " ");
      mid.push(isUnknown ? "x" : changed ? "╳" : "=");
      bottom.push(col === 0 ? (isUnknown ? "x" : "=") : changed ? "┴" : " ");
    }

    previousValue = value;
  }

  return [top.join(""), mid.join(""), bottom.join("")];
}

function cursorMarker(startTime: number, endTime: number, width: number, cursorTime: number): string {
  if (width <= 0) return "";
  const line = Array.from({ length: width }, () => " ");
  const span = Math.max(1, endTime - startTime);
  const pos = Math.max(0, Math.min(width - 1, Math.round(((cursorTime - startTime) / span) * (width - 1))));
  line[pos] = "^";
  return line.join("");
}

function renderAxis(startTime: number, endTime: number, width: number, cursorTime: number): string[] {
  const ticks = [0, 0.25, 0.5, 0.75, 1];
  const tickLine = Array.from({ length: width }, () => "-");
  const labelLine = Array.from({ length: width }, () => " ");
  const cursorLine = Array.from({ length: width }, () => " ");

  for (const ratio of ticks) {
    const pos = Math.max(0, Math.min(width - 1, Math.round((width - 1) * ratio)));
    tickLine[pos] = "|";
  }

  for (let i = 0; i < ticks.length; i++) {
    const label = String(Math.round(startTime + (endTime - startTime) * ticks[i]!));
    const pos = Math.max(0, Math.min(width - 1, Math.round((width - 1) * ticks[i]!)));
    const start = Math.min(width - label.length, Math.max(0, pos - Math.floor(label.length / 2)));
    for (let j = 0; j < label.length && start + j < width; j++) {
      labelLine[start + j] = label[j]!;
    }
  }

  const span = Math.max(1, endTime - startTime);
  const cursorPos = Math.max(0, Math.min(width - 1, Math.round(((cursorTime - startTime) / span) * (width - 1))));
  cursorLine[cursorPos] = "^";

  return [tickLine.join(""), labelLine.join(""), cursorLine.join("")];
}

function summarizeTrace(trace: VcdTrace, kind: string, match?: string): string {
  const signalCount = trace.signals.length;
  const regex = compileRegex(match);
  const filteredCount = regex ? trace.signals.filter((signal) => regex.test(fullName(signal))).length : signalCount;
  return [
    `${kind.toUpperCase()}: ${trace.path}`,
    `Timescale: ${trace.timescale}`,
    `Signals: ${filteredCount}${match ? ` matched / ${signalCount} total` : ""}`,
    `Max time: ${trace.maxTime}`,
  ].join("\n");
}

async function pathExists(pathText: string): Promise<boolean> {
  try {
    await access(pathText, fsConstants.R_OK);
    return true;
  } catch {
    return false;
  }
}

async function findFirstTrace(root: string, maxDepth = 2): Promise<string | undefined> {
  const queue: Array<{ dir: string; depth: number }> = [{ dir: root, depth: 0 }];

  while (queue.length > 0) {
    const { dir, depth } = queue.shift()!;
    let handle;
    try {
      handle = await opendir(dir);
    } catch {
      continue;
    }

    for await (const entry of handle) {
      const entryPath = resolve(dir, entry.name);
      if (entry.isFile() && /\.(vcd|fst)$/i.test(entry.name)) {
        return entryPath;
      }
      if (depth < maxDepth && entry.isDirectory() && !entry.name.startsWith(".")) {
        queue.push({ dir: entryPath, depth: depth + 1 });
      }
    }
  }

  return undefined;
}

async function resolveTracePath(ctx: ExtensionCommandContext, requestedPath?: string): Promise<string | undefined> {
  const cwd = ctx.cwd;

  if (requestedPath) {
    const normalized = normalizeUserPath(requestedPath);
    const resolved = isAbsolute(normalized) ? normalized : resolve(cwd, normalized);
    if (await pathExists(resolved)) return resolved;
  }

  for (const candidate of DEFAULT_TRACE_NAMES) {
    const resolved = resolve(cwd, candidate);
    if (await pathExists(resolved)) return resolved;
  }

  return findFirstTrace(cwd);
}

async function convertFstToVcd(fstPath: string): Promise<TraceSource> {
  const workDir = await mkdtemp(join(tmpdir(), "pi-vcd-"));
  const outputPath = join(workDir, `${basename(fstPath)}.vcd`);
  await execFileAsync("fst2vcd", ["-o", outputPath, fstPath]);
  return {
    path: outputPath,
    originalPath: fstPath,
    displayName: `${basename(fstPath)} → VCD`,
    cleanup: async () => {
      await rm(workDir, { recursive: true, force: true });
    },
  };
}

async function resolveTraceSource(pathText: string): Promise<TraceSource> {
  const ext = extname(pathText).toLowerCase();
  if (ext === ".fst") {
    return convertFstToVcd(pathText);
  }
  return {
    path: pathText,
    originalPath: pathText,
    displayName: basename(pathText),
  };
}

class VcdParser {
  async parse(pathText: string): Promise<VcdTrace> {
    const text = await readFile(pathText, "utf8");
    const signals: VcdSignal[] = [];
    const byCode = new Map<string, VcdSignal>();
    const scopeStack: string[] = [];
    let currentTime = 0;
    let maxTime = 0;
    let timescale = "1 ps";
    let inTimescale = false;
    let timescaleParts: string[] = [];

    for (const rawLine of text.split(/\r?\n/)) {
      const line = rawLine.trim();
      if (!line) continue;

      if (inTimescale) {
        if (line.includes("$end")) {
          const beforeEnd = line.slice(0, line.indexOf("$end")).trim();
          if (beforeEnd) timescaleParts.push(beforeEnd);
          if (timescaleParts.length > 0) timescale = timescaleParts.join(" ");
          inTimescale = false;
          timescaleParts = [];
        } else {
          timescaleParts.push(line);
        }
        continue;
      }

      if (line.startsWith("$timescale")) {
        inTimescale = true;
        const after = line.slice("$timescale".length).trim();
        if (after && !after.includes("$end")) {
          timescaleParts.push(after);
        } else if (after.includes("$end")) {
          const beforeEnd = after.slice(0, after.indexOf("$end")).trim();
          if (beforeEnd) timescaleParts.push(beforeEnd);
          if (timescaleParts.length > 0) timescale = timescaleParts.join(" ");
          inTimescale = false;
          timescaleParts = [];
        }
        continue;
      }

      if (line.startsWith("$scope")) {
        const parts = line.split(/\s+/);
        if (parts.length >= 4) scopeStack.push(parts[3]!);
        continue;
      }

      if (line.startsWith("$upscope")) {
        scopeStack.pop();
        continue;
      }

      if (line.startsWith("$var")) {
        const parts = line.split(/\s+/);
        if (parts.length >= 6) {
          const kind = parts[1]!;
          const width = Number(parts[2] ?? 1);
          const code = parts[3]!;
          const name = parts.slice(4, -1).join(" ");
          const signal: VcdSignal = {
            code,
            scope: [...scopeStack],
            name,
            width: Number.isFinite(width) ? width : 1,
            kind,
            times: [],
            values: [],
          };
          signals.push(signal);
          byCode.set(code, signal);
        }
        continue;
      }

      if (line.startsWith("#")) {
        const time = Number(line.slice(1));
        if (Number.isFinite(time)) {
          currentTime = time;
          maxTime = Math.max(maxTime, time);
        }
        continue;
      }

      const op = line[0];
      if (op === "0" || op === "1" || op === "x" || op === "z" || op === "X" || op === "Z") {
        const code = line.slice(1).trim();
        const signal = byCode.get(code);
        if (signal) this.appendValue(signal, currentTime, op.toLowerCase());
        continue;
      }

      if (op === "b" || op === "B") {
        const spaceIdx = line.indexOf(" ");
        if (spaceIdx > 1) {
          const value = line.slice(1, spaceIdx).trim().toLowerCase();
          const code = line.slice(spaceIdx + 1).trim();
          const signal = byCode.get(code);
          if (signal) this.appendValue(signal, currentTime, value);
        }
      }
    }

    return { path: pathText, timescale, signals, maxTime };
  }

  private appendValue(signal: VcdSignal, time: number, value: string): void {
    const lastIdx = signal.times.length - 1;
    if (lastIdx >= 0) {
      if (signal.times[lastIdx] === time) {
        signal.values[lastIdx] = value;
        return;
      }
      if (signal.values[lastIdx] === value) {
        return;
      }
    }
    signal.times.push(time);
    signal.values.push(value);
  }
}

function buildTree(signals: VcdSignal[], match?: string): TreeScopeNode {
  const regex = compileRegex(match);
  const root: TreeScopeNode = {
    kind: "scope",
    key: "",
    name: "",
    path: [],
    depth: -1,
    children: [],
  };
  const scopeIndex = new Map<string, TreeScopeNode>();
  scopeIndex.set("", root);

  for (const signal of signals) {
    const name = fullName(signal);
    if (regex && !regex.test(name)) continue;
    if (name.startsWith("$rootio.")) continue;

    let parent = root;
    const path: string[] = [];
    for (const segment of signal.scope) {
      path.push(segment);
      const key = scopeKey(path);
      let scopeNode = scopeIndex.get(key);
      if (!scopeNode) {
        scopeNode = {
          kind: "scope",
          key,
          name: segment,
          path: [...path],
          depth: path.length - 1,
          children: [],
        };
        scopeIndex.set(key, scopeNode);
        parent.children.push(scopeNode);
      }
      parent = scopeNode;
    }

    parent.children.push({
      kind: "signal",
      key: signalKey(signal),
      signal,
      depth: signal.scope.length,
    });
  }

  return root;
}

function flattenVisibleItems(root: TreeScopeNode, collapsedScopes: Set<string>): VisibleItem[] {
  const out: VisibleItem[] = [];

  const visit = (node: TreeScopeNode): void => {
    for (const child of node.children) {
      if (child.kind === "scope") {
        out.push({ kind: "scope", key: child.key, depth: child.depth, node: child });
        if (!collapsedScopes.has(child.key)) visit(child);
      } else {
        out.push({ kind: "signal", key: child.key, depth: child.depth, node: child });
      }
    }
  };

  visit(root);
  return out;
}

function firstSignalInScope(node: TreeScopeNode): VcdSignal | undefined {
  for (const child of node.children) {
    if (child.kind === "signal") return child.signal;
    const nested = firstSignalInScope(child);
    if (nested) return nested;
  }
  return undefined;
}

function collectSignals(node: TreeScopeNode, out: VcdSignal[] = []): VcdSignal[] {
  for (const child of node.children) {
    if (child.kind === "signal") {
      out.push(child.signal);
    } else {
      collectSignals(child, out);
    }
  }
  return out;
}

function normalizeSearchText(text: string): string {
  return text.toLowerCase().replace(/\s+/g, " ").trim();
}

function fuzzyScore(query: string, candidate: string): number | null {
  const q = normalizeSearchText(query);
  const c = normalizeSearchText(candidate);
  if (!q) return 0;
  if (!c) return null;

  const exact = c.indexOf(q);
  if (exact >= 0) {
    return exact * 2 + (c.length - q.length);
  }

  let pos = 0;
  let score = 0;
  let matched = 0;
  let lastMatch = -1;

  for (const ch of q) {
    const idx = c.indexOf(ch, pos);
    if (idx < 0) return null;
    if (lastMatch >= 0) {
      score += Math.max(0, idx - lastMatch - 1);
    } else {
      score += idx;
    }
    if (idx === pos) {
      score -= 1;
    }
    matched++;
    lastMatch = idx;
    pos = idx + 1;
  }

  return score * 4 + (c.length - matched);
}

class VcdViewerComponent {
  private readonly tui: { requestRender: () => void };
  private readonly trace: VcdTrace;
  private readonly title: string;
  private readonly onClose: () => void;
  private readonly root: TreeScopeNode;
  private readonly collapsedScopes = new Set<string>();
  private readonly allSignals: VcdSignal[];
  private cursorTime: number;
  private timeSpan: number;
  private fitToTrace = false;
  private searchMode = false;
  private searchQuery = "";
  private searchStatus = "";
  private scrollIndex = 0;
  private selectedIndex = 0;
  private lastWidth = 100;
  private lastVisibleItems: VisibleItem[] = [];

  constructor(
    tui: { requestRender: () => void },
    trace: VcdTrace,
    title: string,
    match: string | undefined,
    onClose: () => void,
  ) {
    this.tui = tui;
    this.trace = trace;
    this.title = title;
    this.onClose = onClose;
    this.root = buildTree(trace.signals, match);
    this.allSignals = collectSignals(this.root);
    this.cursorTime = trace.maxTime > 0 ? Math.floor(trace.maxTime / 2) : 0;
    this.timeSpan = trace.maxTime > 0 ? Math.max(64, Math.min(DEFAULT_WINDOW, trace.maxTime)) : DEFAULT_WINDOW;
  }

  invalidate(): void {
    // Rendering is computed fresh every frame.
  }

  handleInput(data: string): void {
    const items = this.lastVisibleItems.length > 0 ? this.lastVisibleItems : flattenVisibleItems(this.root, this.collapsedScopes);
    const current = items[this.scrollIndex + this.selectedIndex];

    if (this.searchMode) {
      if (matchesKey(data, "escape")) {
        this.searchMode = false;
        this.tui.requestRender();
        return;
      }
      if (matchesKey(data, "backspace")) {
        this.searchQuery = this.searchQuery.slice(0, -1);
        this.updateSearchSelection();
        this.tui.requestRender();
        return;
      }
      if (matchesKey(data, "enter")) {
        this.searchMode = false;
        this.tui.requestRender();
        return;
      }
      if (data.length === 1 && data >= " " && data !== "\u007f") {
        this.searchQuery += data;
        this.updateSearchSelection();
        this.tui.requestRender();
        return;
      }
    }

    if (matchesKey(data, "escape") || matchesKey(data, "ctrl+c") || data === "q" || data === "Q") {
      this.onClose();
      return;
    }

    if (matchesKey(data, "up") || data === "k") {
      if (this.selectedIndex > 0) {
        this.selectedIndex--;
      } else if (this.scrollIndex > 0) {
        this.scrollIndex--;
      }
      this.clampViewport(items);
      this.tui.requestRender();
      return;
    }

    if (matchesKey(data, "down") || data === "j") {
      if (this.selectedIndex < Math.min(this.visibleItemsPerPage() - 1, items.length - 1)) {
        this.selectedIndex++;
      } else if (this.scrollIndex + this.visibleItemsPerPage() < items.length) {
        this.scrollIndex++;
      }
      this.clampViewport(items);
      this.tui.requestRender();
      return;
    }

    if (matchesKey(data, "pageup")) {
      this.scrollIndex = Math.max(0, this.scrollIndex - this.visibleItemsPerPage());
      this.clampViewport(items);
      this.tui.requestRender();
      return;
    }

    if (matchesKey(data, "pagedown")) {
      this.scrollIndex = Math.min(Math.max(0, items.length - this.visibleItemsPerPage()), this.scrollIndex + this.visibleItemsPerPage());
      this.clampViewport(items);
      this.tui.requestRender();
      return;
    }

    if (matchesKey(data, "left") || data === "h") {
      this.fitToTrace = false;
      if (current?.kind === "scope") {
        this.collapsedScopes.add(current.key);
      } else {
        const step = Math.max(1, Math.floor(this.timeSpan / 20));
        this.cursorTime = Math.max(0, this.cursorTime - step);
      }
      this.tui.requestRender();
      return;
    }

    if (matchesKey(data, "right") || data === "l") {
      this.fitToTrace = false;
      if (current?.kind === "scope") {
        this.collapsedScopes.delete(current.key);
      } else {
        const step = Math.max(1, Math.floor(this.timeSpan / 20));
        this.cursorTime = Math.min(this.trace.maxTime, this.cursorTime + step);
      }
      this.tui.requestRender();
      return;
    }

    if (data === " " || matchesKey(data, "enter")) {
      if (current?.kind === "scope") {
        if (this.collapsedScopes.has(current.key)) {
          this.collapsedScopes.delete(current.key);
        } else {
          this.collapsedScopes.add(current.key);
        }
        this.tui.requestRender();
        return;
      }
    }

    if (data === "[") {
      this.fitToTrace = false;
      this.timeSpan = Math.min(Math.max(DEFAULT_WINDOW, this.trace.maxTime || DEFAULT_WINDOW), this.timeSpan * 2);
      this.tui.requestRender();
      return;
    }

    if (data === "]") {
      this.fitToTrace = false;
      this.timeSpan = Math.max(2, Math.floor(this.timeSpan / 2));
      this.tui.requestRender();
      return;
    }

    if (data === "g") {
      this.fitToTrace = false;
      this.cursorTime = 0;
      this.tui.requestRender();
      return;
    }

    if (data === "G") {
      this.fitToTrace = false;
      this.cursorTime = this.trace.maxTime;
      this.tui.requestRender();
      return;
    }

    if (data === "f") {
      this.fitToTrace = true;
      this.cursorTime = 0;
      this.timeSpan = Math.max(DEFAULT_WINDOW, this.trace.maxTime || DEFAULT_WINDOW);
      this.scrollIndex = 0;
      this.selectedIndex = 0;
      this.tui.requestRender();
      return;
    }

    if (data === "/") {
      this.searchMode = true;
      this.searchQuery = "";
      this.searchStatus = "";
      this.tui.requestRender();
      return;
    }

    if (data === "n") {
      this.jumpToChange(+1, items);
      this.tui.requestRender();
      return;
    }

    if (data === "p") {
      this.jumpToChange(-1, items);
      this.tui.requestRender();
      return;
    }
  }

  render(width: number): string[] {
    this.lastWidth = Math.max(60, width);
    const items = flattenVisibleItems(this.root, this.collapsedScopes);
    this.lastVisibleItems = items;
    this.clampViewport(items);

    const signalLabelWidth = Math.max(24, Math.min(56, Math.floor(this.lastWidth * 0.36)));
    const valueWidth = Math.max(14, Math.min(24, Math.floor(this.lastWidth * 0.2)));
    const waveWidth = Math.max(16, this.lastWidth - signalLabelWidth - valueWidth - 8);
    const visibleCount = this.visibleItemsPerPage();
    const startIndex = Math.max(0, this.scrollIndex);
    const endIndex = Math.min(items.length, startIndex + visibleCount);

    const startTime = this.computeWindowStart();
    const endTime = this.computeWindowEnd(startTime);
    const axis = renderAxis(startTime, endTime, waveWidth, this.cursorTime);
    const cursorPos = this.cursorPos(startTime, endTime, waveWidth);

    const selected = items[startIndex + this.selectedIndex];
    const searchSuffix = this.searchQuery ? `  |  search ${this.searchMode ? "/" : ""}${this.searchQuery}${this.searchStatus ? ` (${this.searchStatus})` : ""}` : this.searchMode ? "  |  search /" : "";
    const header = truncateToWidth(
      `VCD Viewer  ${basename(this.trace.path)}  |  ${items.length} visible nodes  |  time ${this.cursorTime}/${this.trace.maxTime} ${this.trace.timescale}  |  ${this.title}${searchSuffix}${selected ? `  |  ${selected.kind === "signal" ? fullName(selected.node.signal) : selected.node.path.join(".")}` : ""}`,
      this.lastWidth,
    );
    const help = truncateToWidth(
      "Keys: ↑↓/jk move  ←→/hl scrub or collapse  / search  space/enter toggle tree  [ ] zoom  g/G start/end  f fit  n/p next/prev change  q quit",
      this.lastWidth,
    );
    const separator = "-".repeat(this.lastWidth);

    const lines: string[] = [header, this.redCursor(axis[0]!, cursorPos), this.redCursor(axis[1]!, cursorPos), this.redCursor(axis[2]!, cursorPos), separator];

    for (let index = startIndex; index < endIndex; index++) {
      const item = items[index]!;
      const selectedRow = index === startIndex + this.selectedIndex;
      lines.push(...this.renderItem(item, selectedRow, signalLabelWidth, valueWidth, waveWidth, startTime, endTime, cursorPos));
    }

    if (startIndex >= endIndex) {
      lines.push(truncateToWidth("(no matching signals)", this.lastWidth));
    }

    lines.push(separator, help);
    return lines;
  }

  private renderItem(
    item: VisibleItem,
    selected: boolean,
    signalLabelWidth: number,
    valueWidth: number,
    waveWidth: number,
    startTime: number,
    endTime: number,
    cursorPos: number,
  ): string[] {
    const prefix = selected ? ">" : " ";
    const indent = "  ".repeat(item.depth);
    const titleWidth = Math.max(20, this.lastWidth - 3);

    if (item.kind === "scope") {
      const scope = item.node;
      const marker = this.collapsedScopes.has(scope.key) ? "[+]" : "[-]";
      const title = truncateToWidth(`${prefix}${indent}${marker} ${scope.path.join(".")}`, titleWidth);
      const detail = truncateToWidth(
        `${prefix}${indent}    ${scope.children.length} child${scope.children.length === 1 ? "" : "ren"}${this.collapsedScopes.has(scope.key) ? "  (collapsed)" : ""}`,
        titleWidth,
      );
      return [title, detail, ""];
    }

    const signal = item.node.signal;
    const name = fullName(signal);
    const value = formatValue(signal, signalAtTime(signal, this.cursorTime));
    const wave = sampleWaveBlock(signal, startTime, endTime, waveWidth);
    const label = `${prefix}${pad(indent + name, signalLabelWidth)} ${pad(value, valueWidth)} | `;
    const spacer = `${prefix}${pad("", signalLabelWidth)} ${pad("", valueWidth)} | `;
    const waveOffset = label.length;
    const spacerOffset = spacer.length;
    return [
      this.redCursor(truncateToWidth(`${label}${wave[0]!}`, this.lastWidth), waveOffset + cursorPos),
      this.redCursor(truncateToWidth(`${spacer}${wave[1]!}`, this.lastWidth), spacerOffset + cursorPos),
      this.redCursor(truncateToWidth(`${spacer}${wave[2]!}`, this.lastWidth), spacerOffset + cursorPos),
      "",
    ];
  }

  private redCursor(line: string, cursorPos: number): string {
    if (cursorPos < 0 || cursorPos >= line.length) return line;
    return `${line.slice(0, cursorPos)}\x1b[31m│\x1b[0m${line.slice(cursorPos + 1)}`;
  }

  private cursorPos(startTime: number, endTime: number, width: number): number {
    if (width <= 0) return 0;
    const span = Math.max(1, endTime - startTime);
    return Math.max(0, Math.min(width - 1, Math.round(((this.cursorTime - startTime) / span) * (width - 1))));
  }

  private updateSearchSelection(): void {
    if (!this.searchQuery) {
      this.searchStatus = "";
      return;
    }

    const best = this.findBestSearchMatch(this.searchQuery);
    if (!best) {
      this.searchStatus = `no match`;
      return;
    }

    this.searchStatus = fullName(best);
    this.revealSignal(best);
  }

  private findBestSearchMatch(query: string): VcdSignal | undefined {
    let bestSignal: VcdSignal | undefined;
    let bestScore = Number.POSITIVE_INFINITY;

    for (const signal of this.allSignals) {
      const candidates = [fullName(signal), signal.name];
      for (const candidate of candidates) {
        const score = fuzzyScore(query, candidate);
        if (score !== null && score < bestScore) {
          bestScore = score;
          bestSignal = signal;
        }
      }
    }

    return bestSignal;
  }

  private revealSignal(signal: VcdSignal): void {
    for (let i = 1; i <= signal.scope.length; i++) {
      this.collapsedScopes.delete(scopeKey(signal.scope.slice(0, i)));
    }

    const items = flattenVisibleItems(this.root, this.collapsedScopes);
    const index = items.findIndex((item) => item.kind === "signal" && item.node.signal.code === signal.code);
    if (index < 0) return;

    const page = this.visibleItemsPerPage();
    const maxTop = Math.max(0, items.length - page);
    this.scrollIndex = Math.max(0, Math.min(maxTop, Math.max(0, index - Math.floor(page / 2))));
    this.selectedIndex = index - this.scrollIndex;
    this.clampViewport(items);
  }

  private visibleItemsPerPage(): number {
    const terminalRows = Math.max(24, process.stdout.rows || 24);
    const chromeRows = 7; // header, 3-line axis, separator, help
    const rowsPerItem = 4; // 3 waveform rows + blank spacer
    return Math.max(1, Math.floor((terminalRows - chromeRows) / rowsPerItem));
  }

  private clampViewport(items: VisibleItem[]): void {
    const page = this.visibleItemsPerPage();
    const maxTop = Math.max(0, items.length - page);
    this.scrollIndex = Math.max(0, Math.min(this.scrollIndex, maxTop));

    if (items.length === 0) {
      this.scrollIndex = 0;
      this.selectedIndex = 0;
      return;
    }

    const maxSelected = Math.max(0, Math.min(page - 1, items.length - this.scrollIndex - 1));
    this.selectedIndex = Math.max(0, Math.min(this.selectedIndex, maxSelected));
  }

  private computeWindowStart(): number {
    if (this.trace.maxTime <= 0) return 0;
    if (this.fitToTrace) return 0;
    const half = Math.floor(this.timeSpan / 2);
    return Math.max(0, Math.min(this.trace.maxTime, this.cursorTime - half));
  }

  private computeWindowEnd(startTime: number): number {
    if (this.fitToTrace) return this.trace.maxTime;
    const end = startTime + this.timeSpan;
    return this.trace.maxTime > 0 ? Math.min(this.trace.maxTime, end) : end;
  }

  private jumpToChange(direction: 1 | -1, items: VisibleItem[]): void {
    const current = items[this.scrollIndex + this.selectedIndex];
    if (!current) return;

    const signal = current.kind === "signal" ? current.node.signal : firstSignalInScope(current.node);
    if (!signal || signal.times.length === 0) return;

    if (direction > 0) {
      const next = signal.times.find((time) => time > this.cursorTime);
      if (next !== undefined) this.cursorTime = next;
      return;
    }

    for (let i = signal.times.length - 1; i >= 0; i--) {
      const time = signal.times[i]!;
      if (time < this.cursorTime) {
        this.cursorTime = time;
        return;
      }
    }
  }
}

async function loadTraceFromSource(source: TraceSource): Promise<VcdTrace> {
  try {
    const parsed = await new VcdParser().parse(source.path);
    return { ...parsed, path: source.originalPath };
  } finally {
    if (source.cleanup) await source.cleanup();
  }
}

async function openTraceViewer(
  ctx: ExtensionCommandContext,
  args: VcdToolParams,
): Promise<{ trace?: VcdTrace; source?: TraceSource; error?: string }> {
  try {
    const resolvedPath = await resolveTracePath(ctx, args.path);
    if (!resolvedPath) {
      return { error: "No .vcd or .fst file found. Pass a path or place dump.vcd / dump.fst in the current directory." };
    }

    const source = await resolveTraceSource(resolvedPath);
    const trace = await loadTraceFromSource(source);

    if (!ctx.hasUI) {
      return { trace, source };
    }

    await ctx.ui.custom((tui, _theme, _kb, done) => {
      return new VcdViewerComponent(tui, trace, source.displayName, args.match, () => done(undefined));
    });

    return { trace, source };
  } catch (error) {
    return { error: error instanceof Error ? error.message : String(error) };
  }
}

export default function (pi: ExtensionAPI) {
  pi.registerTool({
    name: "view_vcd",
    label: "VCD Viewer",
    description: "Open a terminal waveform viewer for a VCD or FST trace",
    promptSnippet: "Inspect RTL waveforms from a VCD/FST trace in a terminal viewer",
    promptGuidelines: [
      "Use view_vcd when the user asks to inspect or debug a waveform trace.",
      "Use view_vcd with dump.vcd or dump.fst in the current directory when the user did not specify a path and a trace is available.",
      "Use view_vcd with --match to narrow the signal list before opening very large traces.",
    ],
    parameters: Type.Object({
      path: Type.Optional(Type.String({ description: "Path to the VCD/FST file" })),
      match: Type.Optional(Type.String({ description: "Regex used to filter signals by hierarchical name" })),
    }),
    execute: async (_toolCallId, params, _signal, _onUpdate, ctx) => {
      const result = await openTraceViewer(ctx, params);
      if (result.error) {
        throw new Error(result.error);
      }

      return {
        content: [{ type: "text", text: summarizeTrace(result.trace!, extname(result.source!.path).toLowerCase() === ".fst" ? "fst" : "vcd", params.match) }],
        details: {
          path: result.source!.path,
          kind: extname(result.source!.path).toLowerCase() === ".fst" ? "fst" : "vcd",
          timescale: result.trace!.timescale,
          signals: result.trace!.signals.length,
          maxTime: result.trace!.maxTime,
        },
      };
    },
  });

  pi.registerCommand("vcd", {
    description: "Open a terminal VCD/FST waveform viewer",
    handler: async (args, ctx) => {
      if (!ctx.hasUI) {
        ctx.ui.notify("VCD viewer requires interactive mode", "warning");
        return;
      }

      let parsed: ParsedArgs;
      try {
        parsed = parseCommandArgs(args);
      } catch (error) {
        ctx.ui.notify(error instanceof Error ? error.message : String(error), "error");
        return;
      }

      try {
        const result = await openTraceViewer(ctx, { path: parsed.path, match: parsed.match });
        if (result.error) {
          ctx.ui.notify(result.error, "error");
          return;
        }

        ctx.ui.notify(`Loaded ${basename(result.source!.originalPath)} (${result.trace!.signals.length} signals)`, "info");
      } catch (error) {
        ctx.ui.notify(error instanceof Error ? error.message : String(error), "error");
      }
    },
  });
}
