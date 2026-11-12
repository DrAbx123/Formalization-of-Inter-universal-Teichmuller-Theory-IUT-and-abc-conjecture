# S2460: permBar cycle type to factorDegrees actual; rootCycleType instance missing

Date: 2026-11-03. Serial -j1.

## Actual

tmp/sheaf/xif/paper/S2460D5CloseActual.lean
  SHA256 86E206B7772AA994AACABC0C33010E162EB7294D4F229EB7F7FA99D56E196732
  EXIT=0
  olean SHA256 C5C92960BCE80E4AD6DDE6CA82E4418DFA60D72427FFE370E9B6D09534CFD365
  size 64296
  axioms propext, Classical.choice, Quot.sound; no sorryAx.

Theorem s2460PermBar_cycleType_factorDegrees:
  (permBar (f := f) p P).cycleType =
    (factorDegrees (fbar f p)).filter (fun n => n != 1).

Proof: S2456 normalization + s2456PermBar_cycleType, then
S2428 filter bridge with hcard identifying fibre ncard with natDegree.

## Exact first missing: rootCycleType transfer instance

Applying s2440_permBar_cycleType_eq_rootCycleType requires an
IsArithFrobAt value whose O_L MulSemiringAction instance is exactly S2440's
local instance
  instMulSemiringActionAlgEquivRingOfIntegers_tmp.
The ambient/global instance
  RingOfIntegers.instMulSemiringAction
is not definitionally the same, so H cannot be used.  The theorem's own
local DecidableEq instances for root sets also differ from S2460's.

Exact goal: restate the S2440 cycle-type transfer with explicit instance
parameters, or provide an instance-transport lemma

  transport IsArithFrobAt across
  MulSemiringAction/DecidableEq equality, and derive

  rootCycleType K L f hsplit sigma
    = (factorDegrees (fbar f p)).filter (· != 1).

Then choose sigma := arithFrobAt via S2167FrobeniusExists to obtain the
corrected Dedekind-Frobenius theorem.  The S2167 existence step also needs
the Finite residue instance; it was not reached.

## Status

- D5 corrected theorem NOT accepted.
- permBar -> factorDegrees step is actual.
- S2427 sorryAx unused; no fake.
