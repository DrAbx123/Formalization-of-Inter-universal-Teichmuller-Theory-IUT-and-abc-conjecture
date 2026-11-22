#!/usr/bin/env node
// FLT v4.35 -> v4.32.2 downgrade pipeline (qpilot, A852/A853)
// Usage: node tools/port_flt_downgrade.mjs --src tmp/external/flt271 --dst tmp/external/ported/flt271 --prefix tmp.external.ported.flt271 --targets FLT.Patching --compile --json tmp/flt271_patching_report.json
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
const args = process.argv.slice(2);
function arg(name, dflt){ const i = args.indexOf('--'+name); return i >= 0 ? args[i+1] : dflt; }
const flag = (name) => args.includes('--'+name);
const SRC = arg('src', 'tmp/external/flt271');
const DST = arg('dst', 'tmp/external/ported/flt271');
const PREFIX = arg('prefix', 'tmp.external.ported.flt271');
const TARGETS = arg('targets', 'FLT.Patching').split(',');
const JSONOUT = arg('json', 'tmp/flt271_port_report.json');
const COMPILE = flag('compile');
const root = process.cwd();

// ---- load rules
const rulesPath = path.join(root, 'tools/port_fix_rules.txt');
const rules = [];
for (const line of fs.readFileSync(rulesPath, 'utf8').split('\n')) {
  if (!line.trim() || line.trim().startsWith('#')) continue;
  const idx = line.indexOf('||');
  if (idx < 0) continue;
  let pat = line.slice(0, idx); const rep = line.slice(idx + 2);
  let flags = 'g';
  if (pat.startsWith('(?m)')) { pat = pat.slice(4); flags = 'gm'; }
  if (pat.includes('(?m)')) { pat = pat.replace('(?m)', ''); flags = 'gm'; }
  rules.push({ pat, rep, flags, label: line.trim() });
}

// ---- module map
const mods = new Map(); const files = new Map();
(function walk(p) {
  for (const e of fs.readdirSync(p, { withFileTypes: true })) {
    if (e.name === '.git' || e.name === '.lake') continue;
    const q = path.join(p, e.name);
    if (e.isDirectory()) walk(q);
    else if (e.name.endsWith('.lean')) {
      const rel = path.relative(SRC, q).split(path.sep).join('/');
      const mod = rel.replace(/\.lean$/, '').replace(/\//g, '.');
      mods.set(mod, rel); files.set(rel, mod);
    }
  }
})(path.join(root, SRC));

function importsOf(rel) {
  const t = fs.readFileSync(path.join(root, SRC, rel), 'utf8');
  return t.split('\n').filter(l => /^\s*(public\s+)?import\s/.test(l))
    .map(l => l.replace(/^\s*(public\s+)?import\s+/, '').trim());
}

// ---- closure of target prefixes
const seen = new Set(); const missing = new Set(); const stack = [];
for (const m of mods.keys()) for (const t of TARGETS) if (m === t || m.startsWith(t + '.')) stack.push(m);
while (stack.length) {
  const m = stack.pop(); if (seen.has(m)) continue; seen.add(m);
  for (const im of importsOf(mods.get(m))) {
    if (mods.has(im)) { if (!seen.has(im)) stack.push(im); }
    else if (im.startsWith('FLT.') || im.startsWith('FermatsLastTheorem')) missing.add(im);
  }
}
const selected = [...seen].sort();

const EXTRA_IMPORTS = [
  { marker: 'compact_exists_isClopen_in_isOpen', importName: 'Mathlib.Topology.Separation.Profinite' },
];

// ---- transform
const ruleHits = {}; const transformed = []; const outFiles = new Map();
for (const m of selected) {
  const rel = mods.get(m);
  let text = fs.readFileSync(path.join(root, SRC, rel), 'utf8');
  // module syntax -> v4.32
  text = text.split('\n').filter(l => !/^\s*module\s*$/.test(l) && !/^\s*public meta import\s/.test(l)).join('\n');
  text = text.replace(/^[ \t]*@\[expose\][ \t]+public[ \t]+section[ \t]*$/gm, 'section');
  text = text.replace(/^[ \t]*@\[expose\][ \t]+section[ \t]*$/gm, 'section');
  text = text.replace(/^[ \t]*public[ \t]+section[ \t]*$/gm, 'section');
  text = text.replace(/^([ \t]*)public[ \t]+import[ \t]+/gm, '$1import ');
  // rewrite internal imports
  text = text.replace(/^([ \t]*)import[ \t]+([A-Za-z0-9_.]+)[ \t]*$/gm, (m0, ws, im) => {
    if (mods.has(im)) return ws + 'import ' + PREFIX + '.' + im;
    return m0;
  });
  // apply generic rules
  for (const r of rules) {
    let n = 0;
    try { text = text.replace(new RegExp(r.pat, r.flags), (...a) => { n++; return (typeof r.rep === 'function') ? r.rep(...a) : r.rep; }); }
    catch (e) { continue; }
    if (n) ruleHits[r.label] = (ruleHits[r.label] || 0) + n;
  }
  // add supplementary imports required by rewritten lemma names
  for (const e of EXTRA_IMPORTS) {
    const impLine = 'import ' + e.importName;
    if (text.includes(e.marker) && !text.includes(impLine)) {
      const lines = text.split('\n');
      let last = -1;
      for (let i = 0; i < lines.length; i++) if (/^\s*import\s/.test(lines[i])) last = i;
      if (last >= 0) lines.splice(last + 1, 0, impLine);
      text = lines.join('\n');
    }
  }
  const outRel = rel;
  const outPath = path.join(root, DST, outRel);
  fs.mkdirSync(path.dirname(outPath), { recursive: true });
  fs.writeFileSync(outPath, text);
  outFiles.set(m, { rel, outRel: outRel, outPath, deps: importsOf(rel).filter(x => mods.has(x) && seen.has(x)) });
  transformed.push({ module: m, rel, outRel });
}

// ---- topological order & compile
const result = { generatedAt: new Date().toISOString(), src: SRC, dst: DST, targets: TARGETS, modules: selected.length, missingExternal: [...missing].sort(), ruleHits, files: [] };
if (COMPILE) {
  const indeg = new Map(selected.map(m => [m, (outFiles.get(m).deps || []).length]));
  const rev = new Map(); for (const m of selected) for (const d of outFiles.get(m).deps) { if (!rev.has(d)) rev.set(d, []); rev.get(d).push(m); }
  const queue = selected.filter(m => indeg.get(m) === 0); const order = [];
  while (queue.length) { const x = queue.shift(); order.push(x); for (const y of (rev.get(x) || [])) { indeg.set(y, indeg.get(y) - 1); if (indeg.get(y) === 0) queue.push(y); } }
  const outRoot = path.join(root, '.lake/build/lib/lean', DST);
  for (const m of order) {
    const f = outFiles.get(m);
    const olean = path.join(outRoot, f.outRel.replace(/\.lean$/, '.olean'));
    fs.mkdirSync(path.dirname(olean), { recursive: true });
    if (fs.existsSync(olean)) { result.files.push({ module: m, exit: 0, ok: true, cached: true }); continue; }
    const log = path.join(root, 'tmp', 'flt271_port_' + m.replace(/\./g, '_') + '.log');
    const r = spawnSync('lake', ['env', 'lean', '-R', DST, '-o', olean, path.join(DST, f.outRel)], { cwd: root, encoding: 'utf8', shell: true, timeout: 900000 });
    try { fs.writeFileSync(log, (r.stdout || '') + (r.stderr || '')); } catch (e) {}
    const ok = r.status === 0 && fs.existsSync(olean);
    let firstError = '';
    try { const lt = fs.readFileSync(log, 'utf8'); const mm = lt.split('\n').find(l => l.includes('error')); firstError = mm || ''; } catch (e) {}
    result.files.push({ module: m, exit: r.status, ok, firstError });
    if (!ok) result.firstFailure = { module: m, exit: r.status, firstError };
    if (!ok) break;
  }
}
fs.writeFileSync(path.join(root, JSONOUT), JSON.stringify(result, null, 2));
console.log(JSON.stringify({ modules: result.modules, missingExternal: result.missingExternal.length, ruleHits: result.ruleHits, compiled: result.files.length, okCount: result.files.filter(f => f.ok).length, firstFailure: result.firstFailure || null }, null, 2));
