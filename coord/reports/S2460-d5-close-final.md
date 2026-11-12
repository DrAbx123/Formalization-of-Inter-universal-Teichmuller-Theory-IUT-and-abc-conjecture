# S2460 final: permBar -> factorDegrees actual; rootCycleType instance missing

Date: 2026-11-03. Serial -j1.

## Actual

tmp/sheaf/xif/paper/S2460D5CloseActual.lean
  SHA256 C7F2E186CDB72E5A80CE1E2B1AC341742FA7E2F6FF434A9DE7A26F64F55F4A6F
  EXIT=0
  olean SHA256 42F821320F1E9DDEB373ADAF1614E319029956A477E8DDBD97E490FAE34F6B29
  size 45824
  axioms propext, Classical.choice, Quot.sound; no sorryAx.

s2460PermBar_cycleType_factorDegrees:
  (permBar (f := f) p P).cycleType =
    (factorDegrees (fbar f p)).filter (fun n => n != 1).

Proof: s2456PermBar_cycleType + s2456_normalization, then
s2408FiberSet_ncard and s2428_filter_fiberSizes_eq_factorDegrees_filter.

## Exact first missing: rootCycleType transfer instance

Applying s2440_permBar_cycleType_eq_rootCycleType requires H with the exact
local O_L MulSemiringAction instance used at S2440 declaration:

  instMulSemiringActionAlgEquivRingOfIntegers_tmp.

An H elaborated under the ambient/global
  RingOfIntegers.instMulSemiringAction
does not match; priority 2000 local instances also do not change the
kernel/typeclass identity.  S2440's local DecidableEq instances on root sets
are a second mismatch.

Required fix: restate the S2440 cycle-type transfer with its instances as
explicit parameters, or prove an instance-transport lemma moving
IsArithFrobAt across equal MulSemiringAction data (and transport the
rootCycleType instance), then:

  rootCycleType K L f hsplit sigma
    = (factorDegrees (fbar f p)).filter (· != 1).

Then sigma := arithFrobAt via S2167FrobeniusExists (plus Finite residue
instance) gives DedekindFrobeniusCycleTypeStatementCorrected and
orbitSizeMultiset.

## Status

- D5 corrected theorem NOT accepted.
- permBar -> factorDegrees bridge is actual.
- S2427 sorryAx unused; no fake.
