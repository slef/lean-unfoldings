// Coherence checks for the book, run after every change (`npm run lint`).
//
// The build (`scripts/build.mjs`) already fails on unknown Lean names, broken
// links and anchors between pages, unknown or uncited bibliography keys, bad
// headline blocks and KaTeX errors. This script checks what the build cannot
// see: prose that refers to the book's structure by number, citations written
// as plain text, and whether the introductions and the preface cover every
// chapter.
//
// Errors exit with status 1. Warnings are printed and do not fail.

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const BOOK = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const REPO = path.resolve(BOOK, '..');
const SRC = path.join(BOOK, 'src');
const CHAPTERS = path.join(SRC, 'chapters');
const DIST = process.env.BOOK_DIST || path.join(BOOK, 'dist');
const VERBOSE = process.argv.includes('--verbose');

const errors = [];
const warnings = [];
const error = (where, msg) => errors.push(`${where}: ${msg}`);
const warn = (where, msg) => warnings.push(`${where}: ${msg}`);

// ---------------------------------------------------------------------------
// Pages, in book order, with the part each one belongs to.

const book = JSON.parse(fs.readFileSync(path.join(SRC, 'book.json'), 'utf8'));
const pages = [];
for (const p of book.front ?? []) pages.push({ ...p, kind: 'front' });
for (const part of book.parts) {
  pages.push({ slug: part.slug, file: part.file, title: part.title, kind: 'part', part });
  for (const ch of part.chapters) {
    pages.push({ ...ch, kind: 'chapter', part });
    for (const sub of ch.children ?? []) pages.push({ ...sub, kind: 'sub', part, parent: ch });
  }
  if (part.notes) pages.push({ ...part.notes, kind: 'notes', part });
}
for (const a of book.appendices ?? []) pages.push({ ...a, kind: 'appendix' });
const bySlug = new Map(pages.map((p) => [p.slug, p]));
for (const p of pages) p.text = fs.readFileSync(path.join(CHAPTERS, p.file), 'utf8');

// Blank out what is not prose, keeping line numbers: code, math, HTML
// comments, links, Lean links, citations and placeholders.
function prose(md) {
  const keepLines = (m) => m.replace(/[^\n]/g, ' ');
  return md
    .replace(/```[\s\S]*?```/g, keepLines)
    .replace(/<!--[\s\S]*?-->/g, keepLines)
    .replace(/\$\$[\s\S]*?\$\$/g, keepLines)
    .replace(/\$[^$\n]*\$/g, keepLines)
    .replace(/`[^`\n]*`/g, keepLines)
    .replace(/\[\[[^\]]*\]\]/g, keepLines)
    .replace(/\[[^\]\n]*\]\([^)\n]*\)/g, keepLines)
    .replace(/\[-?@[^\]\n]*\]/g, keepLines)
    .replace(/-?@[a-z]+[0-9]{4}[a-z]*/g, keepLines)
    .replace(/\{\{(ref|num):[^}]*\}\}/g, keepLines);
}
const lineOf = (text, index) => text.slice(0, index).split('\n').length;

// ---------------------------------------------------------------------------
// 1. Structure referred to by number must be a link, which the build renumbers.
//    Plain "Part I" is allowed only in the introduction of Part I itself. Plain "Section 3"
//    is allowed when it is a section of a paper: the sentence mentions a paper
//    or a citation, or the table's header says "Paper".

const sentenceAround = (text, i) => {
  const start = Math.max(text.lastIndexOf('. ', i), text.lastIndexOf('\n\n', i), 0);
  let end = text.indexOf('. ', i);
  if (end < 0) end = text.length;
  return text.slice(start, end);
};
const tableHeader = (lines, n) => {
  for (let k = n - 1; k >= 0; k--) {
    if (!lines[k].trimStart().startsWith('|')) return '';
    if (k > 0 && !lines[k - 1].trimStart().startsWith('|')) return lines[k];
  }
  return lines[0] ?? '';
};

for (const p of pages) {
  const raw = p.text;
  const text = prose(raw);
  const lines = raw.split('\n');
  const where = (i) => `${p.file}:${lineOf(raw, i)}`;
  for (const m of text.matchAll(/\b(Chapters?|Appendix|Appendices) ([0-9]+|[A-Z])\b/g)) {
    error(where(m.index), `plain "${m[0]}": write it as a link, such as [Chapter 3](accesses.html), or {{ref:slug}}`);
  }
  for (const m of text.matchAll(/\bParts? ((?:[IVX]+)(?:(?:, | and | to )[IVX]+)*)\b/g)) {
    const labels = m[1].split(/, | and | to /);
    // Only a part's own introduction may name itself in plain text.
    if (p.kind === 'part' && labels.length === 1 && labels[0] === p.part.label) continue;
    error(where(m.index), `plain "${m[0]}": link it, such as [Part ${labels[0]}](${book.parts.find((x) => x.label === labels[0])?.slug ?? 'part-…'}.html)`);
  }
  for (const m of text.matchAll(/\bSections? [0-9]+(\.[0-9]+)?\b/g)) {
    const raw_sentence = sentenceAround(raw, m.index);
    if (/paper|@[a-z]+[0-9]{4}|\bthe article\b/i.test(raw_sentence)) continue;
    if (/paper/i.test(tableHeader(lines, lineOf(raw, m.index) - 1))) continue;
    error(where(m.index), `plain "${m[0]}": link sections of the book; a section of a paper must say so ("Section 3 of the paper", or cite it)`);
  }
}

// ---------------------------------------------------------------------------
// 2. Citations written by hand instead of with bibliography keys.

for (const p of pages) {
  const text = prose(p.text);
  const patterns = [
    /(?<![\p{L}])\p{Lu}[\p{L}'’-]+ \((?:19|20)[0-9]{2}[a-z]?[,)]/gu,
    /\((?:[^()\n]*?\p{Lu}[\p{L}'’-]+[^()\n]*?),? (?:19|20)[0-9]{2}[a-z]?\)/gu,
    /\*[^*\n]+\*,? \((?:19|20)[0-9]{2}\)/g,
  ];
  for (const re of patterns) {
    for (const m of text.matchAll(re)) {
      error(`${p.file}:${lineOf(p.text, m.index)}`, `citation in plain text "${m[0]}": use [@key] or @key from book/src/bibliography.json`);
    }
  }
}

// 2b. Citations that render badly, and bibliography metadata.

const bib = JSON.parse(fs.readFileSync(path.join(SRC, 'bibliography.json'), 'utf8')).entries;
const bibByKey = new Map(bib.map((e) => [e.key, e]));
const familyName = (name) => name.trim().split(/\s+/).pop();
for (const p of pages) {
  const raw = p.text.replace(/```[\s\S]*?```/g, (m) => m.replace(/[^\n]/g, ' '));
  // "Sleator and Tarjan [@sleator1985]" renders the names twice: use @key or [-@key].
  for (const m of raw.matchAll(/\[@([a-z]+[0-9]{4}[a-z]*)[^\]]*\]/g)) {
    const e = bibByKey.get(m[1]);
    if (!e) continue;
    const before = raw.slice(Math.max(0, m.index - 40), m.index);
    const name = e.authors.map(familyName).find((n) => before.match(new RegExp(`\\b${n.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}(?: et al\\.)?\\s*$`, 'u')));
    if (name) warn(`${p.file}:${lineOf(p.text, m.index)}`, `${name} is named right before [@${m[1]}], which repeats the name: write @${m[1]} or [-@${m[1]}]`);
  }
  // The same key twice in one sentence.
  for (const sentence of raw.split(/(?<=[.!?])\s+/)) {
    const keys = [...sentence.matchAll(/-?@([a-z]+[0-9]{4}[a-z]*)/g)].map((m) => m[1]);
    const dup = keys.find((k, i) => keys.indexOf(k) !== i);
    if (dup) warn(`${p.file}:${lineOf(p.text, raw.indexOf(sentence))}`, `@${dup} is cited twice in one sentence`);
  }
}
for (const e of bib) {
  const year = Number((e.key.match(/[0-9]{4}/) ?? [])[0]);
  if (year && year !== Number(e.year)) error(`bibliography.json (${e.key})`, `the key says ${year} but the entry's year is ${e.year}`);
  if (e.type === 'article' && !e.pages) warn(`bibliography.json (${e.key})`, 'an article without pages (or "article N")');
}

// ---------------------------------------------------------------------------
// 3. The part introductions and the preface map cover every chapter.

const mentions = (text, slug) => text.includes(`${slug}.html`) || text.includes(`{{num:${slug}}}`) || text.includes(`{{ref:${slug}}}`);
const preface = pages.find((p) => p.slug === 'index');
for (const part of book.parts) {
  const intro = bySlug.get(part.slug);
  const notes = part.notes && bySlug.get(part.notes.slug);
  if (preface && !mentions(preface.text, part.slug)) error(preface.file, `the map of the book does not link Part ${part.label} (${part.slug}.html)`);
  for (const ch of part.chapters) {
    if (!mentions(intro.text, ch.slug)) warn(intro.file, `the introduction of Part ${part.label} does not mention chapter ${ch.slug}`);
    // Notes may skip chapters with no literature behind them: only with --verbose.
    if (VERBOSE && notes && !mentions(notes.text, ch.slug)) warn(notes.file, `the notes of Part ${part.label} do not mention chapter ${ch.slug}`);
    if (preface && !mentions(preface.text, ch.slug)) warn(preface.file, `the map of the book does not mention chapter ${ch.slug}`);
  }
}
const words = ['zero', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine', 'ten'];
for (const m of (preface?.text ?? '').matchAll(/\bhas (\w+) parts\b/g)) {
  if (words.indexOf(m[1]) !== book.parts.length) error(preface.file, `"has ${m[1]} parts", but book.json has ${book.parts.length}`);
}
// ---------------------------------------------------------------------------
// 4. Files under chapters/ that book.json does not list.

const listed = new Set(pages.map((p) => p.file));
for (const dir of fs.readdirSync(CHAPTERS)) {
  for (const f of fs.readdirSync(path.join(CHAPTERS, dir))) {
    if (f.endsWith('.md') && !listed.has(`${dir}/${f}`)) warn(`chapters/${dir}/${f}`, 'not listed in book.json, so it is not rendered');
  }
}

// ---------------------------------------------------------------------------

for (const w of warnings) console.warn(`warning: ${w}`);
for (const e of errors) console.error(`error: ${e}`);
console.log(`lint: ${pages.length} pages, ${errors.length} errors, ${warnings.length} warnings`);
process.exit(errors.length ? 1 : 0);
