#!/usr/bin/env node
// Script migration of the Mathlib 4.36 generalized Ideal.cardQuot_mul lemma into our 4.32.2 tree.
// User directive (2026-11-14): if the 4.36 repo has the corresponding lemma, migrate it by script,
// do NOT re-prove it. Only difference vs 4.32: hypothesis [Infinite S] instead of [Module.Free Z S].
// Usage: node tools/port_mathlib436_absnorm.mjs
import fs from 'node:fs';
import path from 'node:path';
const ROOT = 'D:/lean';
const SRC = path.join(ROOT, 'tmp/mathlib4-4.36.0-rc2/Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean');
const OUTDIR = path.join(ROOT, 'tmp/external/mathlib436_absnorm');
const OUT = path.join(OUTDIR, 'AbsNorm436Port.lean');
const lines = fs.readFileSync(SRC, 'utf8').split(/\r?\n/);
const start = lines.findIndex(l => l.startsWith('theorem cardQuot_mul ['));
if (start < 0) throw new Error('4.36 cardQuot_mul not found');
const endRel = lines.findIndex((l, i) => i > start && l.startsWith('namespace Ring.HasFiniteQuotients'));
if (endRel < 0) throw new Error('block end not found');
let body = lines.slice(start, endRel).join('\n')
  .replace('theorem cardQuot_mul [IsDedekindDomain S] [Infinite S]',
           'theorem cardQuot_mul_unrestricted [IsDedekindDomain S] [Infinite S]');
const headerLines = [
  `/- Script-migrated from Mathlib4 v4.36.0-rc2 Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean.
     The 4.36 lemma is generalized (no Module.Free Z S); our pinned 4.32.2 version has the
     Free-Z hypothesis. Ported mechanically per user directive; not re-proved. -/`,
  'import Mathlib.RingTheory.Ideal.Norm.AbsNorm',
  'import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative',
  'import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas',
  '',
  'noncomputable section',
  'open Submodule',
  '',
  'namespace Mathlib436Port',
  '',
  'variable {S : Type*} [CommRing S]',
  '',
  `/-- Multiplicativity of the ideal norm in Dedekind domains (Mathlib 4.36 statement,
      without Module.Free Z S; migrated by script from 4.36 AbsNorm.lean). -/`,
];
const tail = ['', 'end Mathlib436Port', ''].join('\n');
fs.mkdirSync(OUTDIR, { recursive: true });
fs.writeFileSync(OUT, headerLines.join('\n') + '\n' + body + '\n' + tail);
console.log('wrote ' + OUT + ' (' + body.split('\n').length + ' body lines)');