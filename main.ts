// mend — one patch tool for every AI edit format (SPEC.md v1, sections 1-10).
// Fresh build for round 4: unified diffs, SEARCH/REPLACE blocks, V4A patches and
// JSON tool calls, matched at three tiers, applied atomically or not at all.
// Node 22, standard library alone. Run as `node main.ts [options] [PATCH]`.

import { mkdirSync, readFileSync, readdirSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

/** SPEC 3: a patch's lines are its text split at \n, each with one trailing \r removed. */
function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

/** SPEC 3: a path is safe when not empty, no leading /, no \, no empty/./.. segment. */
function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** SPEC 3: a file's break is CRLF when its first LF follows a CR, else LF. */
function fileBreak(text: string): string {
  const i = text.indexOf('\n');
  return i > 0 && text[i - 1] === '\r' ? '\r\n' : '\n';
}

interface Split {
  lines: string[];
  br: string;
  fin: boolean;
}

/** SPEC 3: split a file's text at its own break; the last empty piece is not a line. */
function splitFile(text: string): Split {
  if (text === '') return { lines: [], br: '\n', fin: false };
  const br = fileBreak(text);
  const fin = text.endsWith(br);
  const parts = text.split(br);
  if (fin) parts.pop();
  return { lines: parts, br, fin };
}

/** SPEC 3: a file of no lines is written empty; otherwise lines joined by its break. */
function joinFile(lines: string[], br: string, fin: boolean): string {
  if (lines.length === 0) return '';
  return lines.join(br) + (fin ? br : '');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted). */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

/** A move that succeeded: its old and new paths, for the section 2 R line. */
interface MoveInfo {
  old: string;
  nw: string;
}
type Edit = (tree: Tree) => MoveInfo | void;

/* ---- section 5: matching lines ---- */

const lead = (s: string): string => (/^[ \t]*/.exec(s) ?? [''])[0]!;
const trimEndST = (s: string): string => s.replace(/[ \t]+$/, '');
const trimST = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');

function lineEq(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return trimEndST(a) === trimEndST(b);
  return trimST(a) === trimST(b);
}

/** All 0-based positions where O occurs in lines at a tier; occurrences may overlap. */
function occurrences(lines: string[], o: string[], tier: number): number[] {
  const out: number[] = [];
  const k = o.length;
  if (k === 0) return out;
  for (let i = 0; i + k <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < k; j++) {
      if (!lineEq(lines[i + j]!, o[j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

interface Found {
  tier: number;
  occ: number[];
}

/** SPEC 5: O is found at the first tier (0, 1, 2; strict: 0 only) where it occurs. */
function findTier(lines: string[], o: string[], strict: boolean): Found | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const occ = occurrences(lines, o, t);
    if (occ.length > 0) return { tier: t, occ };
  }
  return null;
}

/** Like findTier, but only occurrences at/after `from`; for an end-of-file chunk only
    occurrences ending at the file's last line. Returns the first such position. */
function findTierFrom(lines: string[], o: string[], from: number, strict: boolean, eofOnly: boolean): { tier: number; pos: number } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const occ = occurrences(lines, o, t).filter((p) => p >= from && (!eofOnly || p + o.length === lines.length));
    if (occ.length > 0) return { tier: t, pos: occ[0]! };
  }
  return null;
}

interface NPart {
  text: string;
  /** Index into the matched file lines for a context line, null for an added line. */
  fileIdx: number | null;
}

/** SPEC 5: context lines are written as the file's own matched lines. At tier 2 every
    other N line that is not empty and not only whitespace, and starts with P (the leading
    spaces/tabs of O's first line), has that P replaced by F (those of the file's first
    matched line). An empty P is a vacuous prefix, so F is prepended. Tier -1: as-is
    (empty O has no first matched line, so no re-indent applies). */
function buildNew(matched: string[], parts: NPart[], tier: number, oFirst: string): string[] {
  if (tier < 0) return parts.map((p) => (p.fileIdx !== null ? matched[p.fileIdx]! : p.text));
  const f = matched.length > 0 ? lead(matched[0]!) : '';
  const p = lead(oFirst);
  return parts.map((part) => {
    if (part.fileIdx !== null) return matched[part.fileIdx]!;
    const t = part.text;
    if (tier === 2 && t !== '' && t.trim() !== '' && t.startsWith(p)) return f + t.slice(p.length);
    return t;
  });
}

/** SPEC 4: detect the format; a blank line is empty or only whitespace. */
function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/* ---- section 6: unified diffs ---- */

type BodyKind = 'ctx' | 'old' | 'new' | 'bs';
interface BodyLine {
  kind: BodyKind;
  text: string;
}
interface Hunk {
  a: number;
  body: BodyLine[];
}
interface RawSection {
  dashOld: string | null | undefined;
  dashNew: string | null | undefined;
  renameFrom: string | undefined;
  renameTo: string | undefined;
  diffOld: string | undefined;
  diffNew: string | undefined;
  hasDashPair: boolean;
  newFile: boolean;
  deletedFile: boolean;
  sawHunk: boolean;
  hunks: Hunk[];
}

/** A hunk header must match `@@ -A[,B] +C[,D] @@` exactly (single spaces, closing @@),
    optionally followed by any text. Returns A, or null when the line is not one. */
function parseHunkHeader(l: string): number | null {
  const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(l);
  return m ? Number(m[1]) : null;
}

/** `diff --git a/<X> b/<Y>`: split at the FIRST ` b/`; Y is the rest of the line. */
function parseDiffGit(l: string): { x: string; y: string } | null {
  const rest = l.slice('diff --git '.length);
  if (!rest.startsWith('a/')) return null;
  const idx = rest.indexOf(' b/');
  if (idx < 0) return null;
  const x = rest.slice(2, idx);
  const y = rest.slice(idx + 3);
  if (x === '' || y === '') return null;
  return { x, y };
}

/** A `--- ` / `+++ ` path: text after the four characters, up to the first tab,
    with surrounding spaces removed; /dev/null means no file; a leading a/ or b/
    is removed. */
function dashPath(l: string): string | null {
  let t = l.slice(4);
  const tab = t.indexOf('\t');
  if (tab >= 0) t = t.slice(0, tab);
  t = t.trim();
  if (t.startsWith('a/') || t.startsWith('b/')) t = t.slice(2);
  return t === '/dev/null' ? null : t;
}

function newRawSection(): RawSection {
  return {
    dashOld: undefined,
    dashNew: undefined,
    renameFrom: undefined,
    renameTo: undefined,
    diffOld: undefined,
    diffNew: undefined,
    hasDashPair: false,
    newFile: false,
    deletedFile: false,
    sawHunk: false,
    hunks: [],
  };
}

function isSectionStart(l: string, next: string | undefined): boolean {
  return l.startsWith('--- ') && (next ?? '').startsWith('+++ ');
}

/** O is the context and `-` lines, N its context and `+` lines, each in body order.
    `bs` is true only when a `\` line immediately follows the hunk's last context
    or `+` line (section 6: only that suppresses the result's final break). */
function hunkON(body: BodyLine[]): { o: string[]; nParts: NPart[]; bs: boolean } {
  const o: string[] = [];
  const nParts: NPart[] = [];
  let oIdx = 0;
  for (const b of body) {
    if (b.kind === 'ctx') {
      o.push(b.text);
      nParts.push({ text: b.text, fileIdx: oIdx });
      oIdx++;
    } else if (b.kind === 'old') {
      o.push(b.text);
      oIdx++;
    } else if (b.kind === 'new') {
      nParts.push({ text: b.text, fileIdx: null });
    }
  }
  let bs = false;
  let lastIdx = -1;
  body.forEach((b, i) => {
    if (b.kind === 'ctx' || b.kind === 'new') lastIdx = i;
  });
  if (lastIdx >= 0 && body[lastIdx + 1]?.kind === 'bs') bs = true;
  return { o, nParts, bs };
}

/** Apply a section's hunks in order to a file's text. `path` names the file for
    failure lines. Implements the section 6 final-break rule, including the empty-O
    insertion at the end forcing a final break. */
function applyHunks(before: string, hunks: Hunk[], strict: boolean, path: string): string {
  const { lines, br, fin: origFin } = splitFile(before);
  const cur = lines.slice();
  let fin = origFin;
  let d = 0;
  for (const h of hunks) {
    const { o, nParts, bs } = hunkON(h.body);
    if (o.length === 0) {
      const pos = Math.min(Math.max(h.a + d, 0), cur.length);
      const atEnd = pos === cur.length;
      const ins = buildNew([], nParts, -1, '');
      cur.splice(pos, 0, ...ins);
      if (atEnd) fin = !bs;
      d += ins.length;
    } else {
      const found = findTier(cur, o, strict);
      if (!found) throw new Fail('no-match', path);
      const target = h.a - 1 + d;
      let best = found.occ[0]!;
      let bestDist = Math.abs(best - target);
      for (const p of found.occ) {
        const dist = Math.abs(p - target);
        if (dist < bestDist) {
          best = p;
          bestDist = dist;
        }
      }
      const atEnd = best + o.length === cur.length;
      const matched = cur.slice(best, best + o.length);
      const repl = buildNew(matched, nParts, found.tier, o[0]!);
      cur.splice(best, o.length, ...repl);
      if (atEnd) fin = !bs;
      d += repl.length - o.length;
    }
  }
  return joinFile(cur, br, fin);
}

/** A creation is the `+` lines of all its hunks, in order, ended by a line break
    unless a `\` line follows its last `+` line. No `+` lines: an empty file. */
function creationText(hunks: Hunk[]): string {
  const plus: string[] = [];
  let lastHunk = -1;
  let lastPlus = -1;
  hunks.forEach((h, hi) => {
    h.body.forEach((b, bi) => {
      if (b.kind === 'new') {
        plus.push(b.text);
        lastHunk = hi;
        lastPlus = bi;
      }
    });
  });
  if (plus.length === 0) return '';
  let fin = true;
  if (lastHunk >= 0 && hunks[lastHunk]!.body[lastPlus + 1]?.kind === 'bs') fin = false;
  return plus.join('\n') + (fin ? '\n' : '');
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections: RawSection[] = [];
  let cur: RawSection | null = null;
  let i = 0;
  while (i < lines.length) {
    const l = lines[i]!;
    if (l.startsWith('diff --git ')) {
      const dg = parseDiffGit(l);
      if (!dg) throw new Exit2(`error: parse ${i + 1}`);
      cur = newRawSection();
      cur.diffOld = dg.x;
      cur.diffNew = dg.y;
      sections.push(cur);
      i++;
      continue;
    }
    if (isSectionStart(l, lines[i + 1])) {
      if (cur !== null && !cur.sawHunk) {
        // SPEC 6: a section's header stays open until its first hunk, so a second
        // --- / +++ pair before any hunk is part of that header and RE-NAMES
        // the old/new path (last-wins); it does not start a new section.
        cur.dashOld = dashPath(l);
        cur.dashNew = dashPath(lines[i + 1]!);
        cur.hasDashPair = true;
      } else {
        cur = newRawSection();
        cur.dashOld = dashPath(l);
        cur.dashNew = dashPath(lines[i + 1]!);
        cur.hasDashPair = true;
        sections.push(cur);
      }
      i += 2;
      continue;
    }
    if (cur === null) {
      if (l.startsWith('@@')) throw new Exit2(`error: parse ${i + 1}`);
      i++;
      continue;
    }
    if (!cur.sawHunk) {
      if (l.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
      if (l.startsWith('rename from ')) {
        cur.renameFrom = l.slice('rename from '.length).trim();
        i++;
        continue;
      }
      if (l.startsWith('rename to ')) {
        cur.renameTo = l.slice('rename to '.length).trim();
        i++;
        continue;
      }
      if (l.startsWith('new file mode')) {
        cur.newFile = true;
        i++;
        continue;
      }
      if (l.startsWith('deleted file mode')) {
        cur.deletedFile = true;
        i++;
        continue;
      }
      const a = parseHunkHeader(l);
      if (a !== null) {
        cur.sawHunk = true;
        const body: BodyLine[] = [];
        let j = i + 1;
        while (j < lines.length) {
          const bl = lines[j]!;
          if (bl.startsWith('diff --git ')) break;
          if (isSectionStart(bl, lines[j + 1])) break;
          if (bl === '') {
            body.push({ kind: 'ctx', text: '' });
            j++;
            continue;
          }
          const c = bl[0]!;
          if (c === ' ') {
            body.push({ kind: 'ctx', text: bl.slice(1) });
            j++;
            continue;
          }
          if (c === '-') {
            body.push({ kind: 'old', text: bl.slice(1) });
            j++;
            continue;
          }
          if (c === '+') {
            body.push({ kind: 'new', text: bl.slice(1) });
            j++;
            continue;
          }
          if (c === '\\') {
            body.push({ kind: 'bs', text: bl.slice(1) });
            j++;
            continue;
          }
          break;
        }
        while (body.length > 0 && body[body.length - 1]!.kind === 'ctx' && body[body.length - 1]!.text === '') body.pop();
        cur.hunks.push({ a, body });
        i = j;
        continue;
      }
      if (l.startsWith('@@')) throw new Exit2(`error: parse ${i + 1}`);
      i++;
      continue;
    }
    const a = parseHunkHeader(l);
    if (a !== null) {
      const body: BodyLine[] = [];
      let j = i + 1;
      while (j < lines.length) {
        const bl = lines[j]!;
        if (bl.startsWith('diff --git ')) break;
        if (isSectionStart(bl, lines[j + 1])) break;
        if (bl === '') {
          body.push({ kind: 'ctx', text: '' });
          j++;
          continue;
        }
        const c = bl[0]!;
        if (c === ' ') {
          body.push({ kind: 'ctx', text: bl.slice(1) });
          j++;
          continue;
        }
        if (c === '-') {
          body.push({ kind: 'old', text: bl.slice(1) });
          j++;
          continue;
        }
        if (c === '+') {
          body.push({ kind: 'new', text: bl.slice(1) });
          j++;
          continue;
        }
        if (c === '\\') {
          body.push({ kind: 'bs', text: bl.slice(1) });
          j++;
          continue;
        }
        break;
      }
      while (body.length > 0 && body[body.length - 1]!.kind === 'ctx' && body[body.length - 1]!.text === '') body.pop();
      cur.hunks.push({ a, body });
      i = j;
      continue;
    }
    if (l.startsWith('@@')) throw new Exit2(`error: parse ${i + 1}`);
    i++;
  }
  return sections.map((sec) => sectionEdit(sec, strict));
}

/** First value that is defined; null counts as defined (it means /dev/null). */
function firstDef<T>(...vs: (T | undefined)[]): T | undefined {
  for (const v of vs) if (v !== undefined) return v;
  return undefined;
}

function sectionEdit(sec: RawSection, strict: boolean): Edit {
  const oldRaw = firstDef(sec.dashOld, sec.renameFrom, sec.diffOld);
  const newRaw = firstDef(sec.dashNew, sec.renameTo, sec.diffNew);
  // D39 (SPEC 6): `/dev/null` means no file, for the RESOLVED path from ANY
  // source — dash (already null via dashPath), rename from/to, or diff --git.
  const oldPath = oldRaw === '/dev/null' ? null : oldRaw;
  const newPath = newRaw === '/dev/null' ? null : newRaw;
  const oldNull = oldPath === null;
  const newNull = newPath === null;
  if (oldNull || sec.newFile) {
    const p = newPath ?? '/dev/null';
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, creationText(sec.hunks));
    };
  }
  if (newNull || sec.deletedFile) {
    const p = oldPath ?? '/dev/null';
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) === null) throw new Fail('missing', p);
      tree.now.set(p, null);
    };
  }
  if (oldPath !== newPath) {
    const o = oldPath as string;
    const n = newPath as string;
    return (tree) => {
      if (!safe(o)) throw new Fail('unsafe', o);
      if (!safe(n)) throw new Fail('unsafe', n);
      const before = tree.get(o);
      if (before === null) throw new Fail('missing', o);
      if (tree.get(n) !== null) throw new Fail('exists', n);
      const out = applyHunks(before, sec.hunks, strict, o);
      tree.now.set(o, null);
      tree.now.set(n, out);
      return { old: o, nw: n };
    };
  }
  const p = oldPath as string;
  return (tree) => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const before = tree.get(p);
    if (before === null) throw new Fail('missing', p);
    tree.now.set(p, applyHunks(before, sec.hunks, strict, p));
  };
}

/* ---- section 7: SEARCH/REPLACE blocks ---- */

function srEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
      return;
    }
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    const { lines, br, fin } = splitFile(before);
    const found = findTier(lines, oldLines, strict);
    if (!found) throw new Fail('no-match', path);
    if (found.occ.length > 1) throw new Fail('ambiguous', path);
    const pos = found.occ[0]!;
    const matched = lines.slice(pos, pos + oldLines.length);
    const repl = buildNew(matched, newLines.map((t) => ({ text: t, fileIdx: null })), found.tier, oldLines[0]!);
    lines.splice(pos, oldLines.length, ...repl);
    tree.now.set(path, joinFile(lines, br, fin));
  };
}

function srEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevPath: string | null = null;
  let prevEnd = -1;
  let i = 0;
  for (;;) {
    let s = -1;
    for (let j = i; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') {
        s = j;
        break;
      }
    }
    if (s < 0) break;
    let path: string | null = null;
    for (let j = s - 1; j > prevEnd; j--) {
      const l = lines[j]!;
      if (blank(l)) continue;
      const t = l.trim();
      if (t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${s + 1}`);
      path = prevPath;
    }
    let eq = -1;
    let rep = -1;
    for (let j = s + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '=======') {
        eq = j;
        break;
      }
    }
    if (eq >= 0) {
      for (let j = eq + 1; j < lines.length; j++) {
        if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
          rep = j;
          break;
        }
      }
    }
    if (eq < 0 || rep < 0) throw new Exit2(`error: parse ${s + 1}`);
    edits.push(srEdit(path, lines.slice(s + 1, eq), lines.slice(eq + 1, rep), strict));
    prevPath = path;
    prevEnd = rep;
    i = rep + 1;
  }
  return edits;
}

/* ---- section 8: V4A patches ---- */

interface Chunk {
  anchor: string | null;
  eof: boolean;
  body: BodyLine[];
}

function chunkON(chunk: Chunk): { o: string[]; nParts: NPart[] } {
  const o: string[] = [];
  const nParts: NPart[] = [];
  let oIdx = 0;
  for (const b of chunk.body) {
    if (b.kind === 'ctx') {
      o.push(b.text);
      nParts.push({ text: b.text, fileIdx: oIdx });
      oIdx++;
    } else if (b.kind === 'old') {
      o.push(b.text);
      oIdx++;
    } else if (b.kind === 'new') {
      nParts.push({ text: b.text, fileIdx: null });
    }
  }
  return { o, nParts };
}

function v4aHeader(l: string, prefix: string): string | null {
  return l.startsWith(prefix) ? l.slice(prefix.length).trim() : null;
}

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let j = lines.length - 1; j >= 0; j--) {
    if (!blank(lines[j]!)) {
      last = j;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const l = lines[i]!;
    if (blank(l)) {
      i++;
      continue;
    }
    const addPath = v4aHeader(l, '*** Add File: ');
    const delPath = addPath === null ? v4aHeader(l, '*** Delete File: ') : null;
    const updPath = addPath === null && delPath === null ? v4aHeader(l, '*** Update File: ') : null;
    if (addPath === null && delPath === null && updPath === null) throw new Exit2(`error: parse ${i + 1}`);
    if (addPath !== null) {
      const items: { text: string; rawBlank: boolean }[] = [];
      let j = i + 1;
      while (j < last) {
        const bl = lines[j]!;
        if (v4aHeader(bl, '*** Add File: ') !== null || v4aHeader(bl, '*** Delete File: ') !== null || v4aHeader(bl, '*** Update File: ') !== null) break;
        if (bl.startsWith('+')) {
          items.push({ text: bl.slice(1), rawBlank: false });
          j++;
          continue;
        }
        if (bl === '') {
          items.push({ text: '', rawBlank: true });
          j++;
          continue;
        }
        throw new Exit2(`error: parse ${j + 1}`);
      }
      while (items.length > 0 && items[items.length - 1]!.rawBlank) items.pop();
      const text = items.length === 0 ? '' : items.map((x) => x.text).join('\n') + '\n';
      const p = addPath;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, text);
      });
      i = j;
      continue;
    }
    if (delPath !== null) {
      let j = i + 1;
      while (j < last) {
        const bl = lines[j]!;
        if (v4aHeader(bl, '*** Add File: ') !== null || v4aHeader(bl, '*** Delete File: ') !== null || v4aHeader(bl, '*** Update File: ') !== null) break;
        if (blank(bl)) {
          j++;
          continue;
        }
        throw new Exit2(`error: parse ${j + 1}`);
      }
      const p = delPath;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
      });
      i = j;
      continue;
    }
    const p = updPath!;
    const updLine = i;
    let j = i + 1;
    let moveTo: string | null = null;
    if (j < last && lines[j]!.startsWith('*** Move to: ')) {
      moveTo = lines[j]!.slice('*** Move to: '.length).trim();
      j++;
    }
    let chunks: Chunk[] = [];
    let curChunk: Chunk | null = null;
    while (j < last) {
      const bl = lines[j]!;
      if (v4aHeader(bl, '*** Add File: ') !== null || v4aHeader(bl, '*** Delete File: ') !== null || v4aHeader(bl, '*** Update File: ') !== null) break;
      if (bl.startsWith('@@')) {
        const anchor = bl.slice(2).trim();
        curChunk = { anchor: anchor === '' ? null : anchor, eof: false, body: [] };
        chunks.push(curChunk);
        j++;
        continue;
      }
      if (bl === '*** End of File') {
        if (curChunk === null) throw new Exit2(`error: parse ${j + 1}`);
        curChunk.eof = true;
        curChunk = null;
        j++;
        continue;
      }
      if (bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+') || bl === '') {
        const item: BodyLine = bl === '' ? { kind: 'ctx', text: '' } : bl[0] === ' ' ? { kind: 'ctx', text: bl.slice(1) } : bl[0] === '-' ? { kind: 'old', text: bl.slice(1) } : { kind: 'new', text: bl.slice(1) };
        if (curChunk !== null) {
          curChunk.body.push(item);
          j++;
          continue;
        }
        if (chunks.length === 0) {
          curChunk = { anchor: null, eof: false, body: [item] };
          chunks.push(curChunk);
          j++;
          continue;
        }
        if (bl === '') {
          j++;
          continue;
        }
        throw new Exit2(`error: parse ${j + 1}`);
      }
      throw new Exit2(`error: parse ${j + 1}`);
    }
    if (curChunk !== null) {
      while (curChunk.body.length > 0 && curChunk.body[curChunk.body.length - 1]!.kind === 'ctx' && curChunk.body[curChunk.body.length - 1]!.text === '') curChunk.body.pop();
    }
    chunks = chunks.filter((c) => c.anchor !== null || c.body.length > 0);
    if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${updLine + 1}`);
    const move = moveTo;
    const myChunks = chunks;
    edits.push((tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (move !== null && !safe(move)) throw new Fail('unsafe', move);
      const before = tree.get(p);
      if (before === null) throw new Fail('missing', p);
      if (move !== null && tree.get(move) !== null) throw new Fail('exists', move);
      const { lines: origLines, br, fin } = splitFile(before);
      const cur = origLines.slice();
      let cursor = 0;
      for (const ch of myChunks) {
        if (ch.anchor !== null) {
          const f = findTierFrom(cur, [ch.anchor], cursor, strict, false);
          if (!f) throw new Fail('no-match', p);
          cursor = f.pos + 1;
        }
        const { o, nParts } = chunkON(ch);
        if (o.length === 0) {
          const pos = ch.eof ? cur.length : cursor;
          const ins = buildNew([], nParts, -1, '');
          cur.splice(pos, 0, ...ins);
          cursor = pos + ins.length;
        } else {
          const f = findTierFrom(cur, o, cursor, strict, ch.eof);
          if (!f) throw new Fail('no-match', p);
          const matched = cur.slice(f.pos, f.pos + o.length);
          const repl = buildNew(matched, nParts, f.tier, o[0]!);
          cur.splice(f.pos, o.length, ...repl);
          cursor = f.pos + repl.length;
        }
      }
      const out = joinFile(cur, br, fin);
      if (move !== null) {
        tree.now.set(p, null);
        tree.now.set(move, out);
        return { old: p, nw: move };
      }
      tree.now.set(p, out);
    });
    i = j;
  }
  return edits;
}

/* ---- section 9: JSON edits ---- */

/** One JSON edit object, or null when it is not one. A wrong command or a missing
    or mistyped key is a parse fault; the only exception is str_replace's new_str,
    which is empty when absent. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const { lines, br, fin } = splitFile(before);
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, joinFile(lines, br, fin));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, idx) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${idx + 1}`);
    edits.push(e);
  });
  return edits;
}

/* ---- sections 1, 2 and 10: invocation, output, order and atomicity ---- */

function byteCmp(a: string, b: string): number {
  return Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8'));
}

/** Remove a directory when it is left empty by a deletion, so a later write can
    take its path as a file. Only ancestors of deleted files are tried. */
function pruneEmptyDirs(p: string): void {
  let d = dirname(p);
  while (d !== '.' && d !== '') {
    try {
      if (readdirSync(d).length !== 0) return;
    } catch {
      return;
    }
    try {
      rmSync(d);
    } catch {
      return;
    }
    d = dirname(d);
  }
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines, strict);
    else if (kind === 'search-replace') edits = srEdits(lines, strict);
    else edits = v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  const moves: MoveInfo[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      const r = edit(tree);
      if (r) moves.push(r);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const deleted = new Set<string>();
  const added = new Set<string>();
  const modified: string[] = [];
  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (was === null) added.add(p);
    else if (now === null) deleted.add(p);
    else modified.push(p);
  }
  const rows: { key: string; text: string }[] = [];
  for (const m of moves) {
    if (deleted.has(m.old) && added.has(m.nw)) {
      deleted.delete(m.old);
      added.delete(m.nw);
      rows.push({ key: m.nw, text: `R ${m.old} -> ${m.nw}` });
    }
  }
  for (const p of deleted) rows.push({ key: p, text: `D ${p}` });
  for (const p of added) rows.push({ key: p, text: `A ${p}` });
  for (const p of modified) rows.push({ key: p, text: `M ${p}` });
  rows.sort((a, b) => byteCmp(a.key, b.key));
  if (!check) {
    const changed = [...tree.now.keys()].sort(byteCmp);
    for (const p of changed) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) {
        rmSync(p, { force: true });
        pruneEmptyDirs(p);
      }
    }
    for (const p of changed) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now || now === null) continue;
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, now);
    }
  }
  return { code: 0, out: [...rows.map((r) => r.text), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
