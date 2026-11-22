#!/usr/bin/env node
// Port tmp/external/iut4-sec1 (IUT IV §1) into tmp/sheaf/iut4sec1,
// rewriting module imports Iut4Sec1.* -> tmp.sheaf.iut4sec1.Iut4Sec1.*
import { readFileSync, writeFileSync, mkdirSync, readdirSync, statSync, existsSync } from 'node:fs';
import { join, relative, dirname } from 'node:path';

const ROOT = 'D:/lean';
const SRC = join(ROOT, 'tmp/external/iut4-sec1');
const SRC_PKG = join(SRC, 'Iut4Sec1');
const DST = join(ROOT, 'tmp/sheaf/iut4sec1');
const DST_PKG = join(DST, 'Iut4Sec1');
const IMPORT_OLD = /^import Iut4Sec1\./gm;
const IMPORT_NEW = 'import tmp.sheaf.iut4sec1.Iut4Sec1.';

if (!existsSync(SRC_PKG)) { console.error('missing source package '+SRC_PKG); process.exit(1); }

const HEADER = (src) =>
  '/- Ported from tmp/external/iut4-sec1 (IUT IV section 1).\n' +
  'Source: ' + src + '.  Imports rewritten to the tmp.sheaf.iut4sec1 namespace;\n' +
  'mathematical content unchanged. -/\n';

function walk(dir) {
  const out = [];
  for (const e of readdirSync(dir, { withFileTypes: true })) {
    const p = join(dir, e.name);
    if (e.isDirectory()) out.push(...walk(p));
    else if (e.name.endsWith('.lean')) out.push(p);
  }
  return out;
}

const files = walk(SRC_PKG);
if (existsSync(join(SRC, 'Iut4Sec1.lean'))) files.push(join(SRC, 'Iut4Sec1.lean'));

const copied = [];
for (const src of files) {
  const rel = relative(SRC, src).replace(/\\/g, '/');
  const dst = join(DST, rel);
  let text = readFileSync(src, 'utf8');
  const before = text;
  text = text.replace(IMPORT_OLD, IMPORT_NEW);
  // Root module `import Iut4Sec1` (without dot) is not used; guard anyway.
  if (text === before && rel === 'Iut4Sec1.lean') {
    text = text.replace(/^import Iut4Sec1$/gm, 'import tmp.sheaf.iut4sec1.Iut4Sec1');
  }
  const header = HEADER(rel);
  if (!text.startsWith('/-! Ported from')) text = header + text;
  mkdirSync(dirname(dst), { recursive: true });
  writeFileSync(dst, text);
  copied.push({ src: rel, dst: relative(ROOT, dst).replace(/\\/g, '/') });
}

console.log(JSON.stringify({ copied: copied.length, files: copied }, null, 1));
