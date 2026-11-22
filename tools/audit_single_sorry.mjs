#!/usr/bin/env node
// tools/audit_single_sorry.mjs  (A871)
// Single-sorry policy audit: exactly ONE allowed sorry in the whole chain:
//   tmp/sheaf/xif/paper/Mzk1IUTModuloSSIneq.lean :: theorem ssIneq_sorry
// Any other sorry/admit/axiom (outside comments) is a FAIL.
// Usage: node tools/audit_single_sorry.mjs [--json out.json]
import { readFileSync, writeFileSync, readdirSync, existsSync } from 'node:fs';
import { join, sep } from 'node:path';
const ROOTS = ['tmp/sheaf/xif/paper', 'LeanFormal'];

// Final-chain files (curated; expand as the chain stabilizes).
const CHAIN = [
  'tmp/sheaf/xif/paper/Mzk1IUTModuloSSIneq.lean',
  'tmp/sheaf/xif/paper/Mzk1FinalConditionalABCActual.lean',
  'tmp/sheaf/xif/paper/Mzk1FinalBoundaryCertificateV2Actual.lean',
  'tmp/sheaf/xif/paper/Mzk1CRouteAssemblyActual.lean',
  'tmp/sheaf/xif/paper/Mzk1E7ReductionActual.lean',
  'tmp/sheaf/xif/paper/Mzk1DExactLowerActual.lean',
  'tmp/sheaf/xif/paper/Mzk1FreyConductorFinalActual.lean',
];
const ALLOW = [{ file: 'tmp/sheaf/xif/paper/Mzk1IUTModuloSSIneq.lean', decl: 'ssIneq_sorry' }];
function* walk(dir) {
  let entries;
  try { entries = readdirSync(dir, { withFileTypes: true }); } catch { return; }
  for (const e of entries) {
    const p = join(dir, e.name);
    if (e.isDirectory()) { if (e.name === '.lake' || e.name === '.git') continue; yield* walk(p); }
    else if (e.name.endsWith('.lean')) yield p;
  }
}

// Strip nested block comments and line comments (approximation; Lean strings are rare here).
function stripComments(text) {
  let out = '';
  let i = 0;
  const n = text.length;
  while (i < n) {
    if (text[i] === '/' && text[i + 1] === '-') {
      let depth = 1; i += 2;
      while (i < n && depth > 0) {
        if (text[i] === '/' && text[i + 1] === '-') { depth++; i += 2; }
        else if (text[i] === '-' && text[i + 1] === '/') { depth--; i += 2; }
        else i++;
      }
      continue;
    }
    if (text[i] === '-' && text[i + 1] === '-') { while (i < n && text[i] !== '\n') i++; continue; }
    out += text[i]; i++;
  }
  return out;
}

// Remove string literals (approximation) so a quoted "sorry" is not counted.
function stripStrings(text) {
  let out = '';
  let i = 0;
  const n = text.length;
  while (i < n) {
    const c = text[i];
    if (c === '"' || c === "'") {
      const q = c; i++;
      while (i < n) {
        if (text[i] === '\\') { i += 2; continue; }
        if (text[i] === q) { i++; break; }
        i++;
      }
      continue;
    }
    out += c; i++;
  }
  return out;
}
function lineOf(text, idx) {
  let l = 1;
  for (let i = 0; i < idx && i < text.length; i++) if (text[i] === '\n') l++;
  return l;
}
function enclosingDecl(code, idx) {
  const before = code.slice(0, idx);
  const re = /\b(theorem|lemma|example|def|instance)\s+([A-Za-z0-9_'.]+)/g;
  let m, last = null;
  while ((m = re.exec(before)) !== null) last = m[2];
  return last;
}

function main() {
  const args = process.argv.slice(2);
  const chainMode = args.includes('--chain');
  const chainStats = [];
  if (chainMode) {
    for (const f of CHAIN) {
      if (!existsSync(f)) { chainStats.push({ file: f, status: 'MISSING' }); continue; }
      const code = stripStrings(stripComments(readFileSync(f, 'utf8')));
      const n = (code.match(/\bsorry\b/g) || []).length;
      const ax = (code.match(/(^|\n)\s*axiom\s+[A-Za-z0-9_'.]+/g) || []).length;
      chainStats.push({ file: f, sorry: n, axiom: ax });
    }
    console.log('## chain scan');
    for (const c of chainStats) console.log(JSON.stringify(c));
  }
  if (args.includes('--sequence')) {
    const lines = [
      '## Acceptance sequence (single-sorry policy, A873)',
      '1) with the one sorry (after lana oleans exist):',
      '   lake env lean tmp/sheaf/xif/paper/Mzk1IUTModuloSSIneq.lean',
      '   # expect EXIT=0 + warning: declaration uses sorry',
      '2) axioms probe:',
      '   printf import-probe > tmp/a873_probe.lean then: lake env lean tmp/a873_probe.lean',
      '   # expect exactly one sorryAx in the printed axiom list',
      '3) remove the sorry on a COPY (replace by-newline-sorry with by), then:',
      '   lake env lean <copy>.lean ; # MUST fail with unsolved goals (exit 1)',
      '4) full scan: node tools/audit_single_sorry.mjs --chain --json tmp/single_sorry.json',
    ];
    for (const l of lines) console.log(l);
    if (args.includes('--only-sequence')) process.exit(0);
  }

  let jsonOut = null;
  const ji = args.indexOf('--json');
  if (ji >= 0) jsonOut = args[ji + 1] || 'single_sorry_report.json';
  const violations = [];
  const allowed = [];
  const errors = [];
  let files = 0;
  for (const root of ROOTS) {
    if (!existsSync(root)) { errors.push('missing root: ' + root); continue; }
    for (const file of walk(root)) {
      files++;
      let text;
      try { text = readFileSync(file, 'utf8'); } catch (e) { errors.push(file + ': ' + e.message); continue; }
      const code = stripStrings(stripComments(text));
      const norm = file.split(sep).join('/');
      const isAllowedFile = ALLOW.some(a => a.file === norm);
      const re = /\bsorry\b/g;
      let m;
      while ((m = re.exec(code)) !== null) {
        const line = lineOf(code, m.index);
        const decl = enclosingDecl(code, m.index);
        const hit = { kind: 'sorry', file: norm, line, decl };
        const ok = isAllowedFile && ALLOW.some(a => a.file === norm && decl === a.decl);
        (ok ? allowed : violations).push(hit);
      }
      const reA = /\badmit\b/g;
      while ((m = reA.exec(code)) !== null) {
        violations.push({ kind: 'admit', file: norm, line: lineOf(code, m.index), decl: enclosingDecl(code, m.index) });
      }
      const reAx = /(^|\n)\s*axiom\s+([A-Za-z0-9_'.]+)/g;
      while ((m = reAx.exec(code)) !== null) {
        violations.push({ kind: 'axiom', file: norm, line: lineOf(code, m.index), decl: m[2] });
      }
    }
  }
  const report = {
    generated_at: new Date().toISOString(),
    roots: ROOTS,
    allowlist: ALLOW,
    files_scanned: files,
    allowed_count: allowed.length,
    allowed,
    violation_count: violations.length,
    violations,
    errors,
  };
  console.log('single-sorry audit: files=' + files + ' allowed=' + allowed.length + ' violations=' + violations.length);
  for (const a of allowed) console.log('  ALLOWED ' + a.file + ':' + a.line + ' (' + a.decl + ')');
  for (const v of violations.slice(0, 50)) console.log('  VIOLATION ' + v.kind + ' ' + v.file + ':' + v.line + ' (' + (v.decl || '?') + ')');
  if (violations.length > 50) console.log('  ... and ' + (violations.length - 50) + ' more');
  if (jsonOut) { writeFileSync(jsonOut, JSON.stringify(report, null, 1)); console.log('json: ' + jsonOut); }
  process.exit(violations.length === 0 ? 0 : 1);
}
try { main(); } catch (e) { console.error('audit error: ' + (e && e.message ? e.message : e)); process.exit(2); }
