#!/usr/bin/env node
// wd_preflight.mjs — check import oleans before queuing Lean targets.
// Usage: node tools/wd_preflight.mjs [--apply]
import fs from 'node:fs';
import path from 'node:path';

const ROOT = 'D:/lean';
const WL = path.join(ROOT, 'dag/watchdog/extra-targets.txt');
const DEF = path.join(ROOT, 'dag/watchdog/deferred-targets.txt');
const REPORT = path.join(ROOT, 'dag/watchdog/preflight-report.json');

function roots() {
  const rs = [path.join(ROOT, '.lake/build/lib/lean')];
  const pkg = path.join(ROOT, '.lake/packages');
  if (fs.existsSync(pkg)) {
    for (const d of fs.readdirSync(pkg)) {
      const r = path.join(pkg, d, '.lake/build/lib/lean');
      if (fs.existsSync(r)) rs.push(r);
    }
  }
  // toolchain oleans (Lean/Std)
  const elan = 'C:/Users/Administrator/.elan/toolchains';
  if (fs.existsSync(elan)) {
    for (const d of fs.readdirSync(elan)) {
      const r = path.join(elan, d, 'lib/lean');
      if (fs.existsSync(r)) rs.push(r);
    }
  }
  return rs;
}
const RS = roots();
const modPath = (m) => m.replace(/\./g, '/') + '.olean';
const hasOlean = (m) => RS.some((r) => fs.existsSync(path.join(r, modPath(m))));

function importsOf(file) {
  try {
    const t = fs.readFileSync(path.join(ROOT, file), 'utf8');
    return [...t.matchAll(/^\s*import\s+([^\s]+)/gm)].map((x) => x[1]);
  } catch { return null; }
}
function check(file) {
  const imps = importsOf(file);
  if (!imps) return { file, ready: false, missing: ['<source missing>'] };
  const missing = imps.filter((m) => !hasOlean(m));
  return { file, ready: missing.length === 0, missing };
}

const apply = process.argv.includes('--apply');
const current = fs.readFileSync(WL, 'utf8').split(/\r?\n/).map((s) => s.trim()).filter(Boolean);
const deferredPrev = fs.existsSync(DEF) ? fs.readFileSync(DEF, 'utf8').split(/\r?\n/).map((s) => s.trim()).filter(Boolean) : [];
const universe = [...new Set([...current, ...deferredPrev])];
const results = universe.map(check);
const ready = results.filter((r) => r.ready).map((r) => r.file);
const blocked = results.filter((r) => !r.ready);
fs.writeFileSync(REPORT, JSON.stringify({ generatedAt: new Date().toISOString(), total: universe.length, ready: ready.length, blocked: blocked.length, blockedList: blocked }, null, 2) + '\n');
console.log('total=' + universe.length + ' ready=' + ready.length + ' blocked=' + blocked.length);
for (const b of blocked.slice(0, 10)) console.log('BLOCKED ' + b.file + ' <- ' + b.missing.slice(0, 2).join(', '));
if (apply) {
  fs.writeFileSync(WL, ready.join('\n') + (ready.length ? '\n' : ''));
  fs.writeFileSync(DEF, blocked.map((b) => b.file).join('\n') + (blocked.length ? '\n' : ''));
  console.log('APPLIED: whitelist=' + ready.length + ' deferred=' + blocked.length);
}
