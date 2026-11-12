# S2460: rootCycleType = factorDegrees.filter actual

Date: 2026-11-03. Serial -j1.

## Actual

tmp/sheaf/xif/paper/S2460D5CloseActual.lean
  SHA256 BF1CC76CD47CA165BF8A40C6B5563E92C4A128F0B0E23484C35AD2693C7333DF
  EXIT=0
  olean SHA256 37688E1D923C4A266C49E2DC599EFF839AF46F865948846B95C7A4B8F730A115
  size 77032
  axioms propext, Classical.choice, Quot.sound; no sorryAx.

Two theorems:
- s2460PermBar_cycleType_factorDegrees:
    (permBar f p P).cycleType = factorDegrees.filter (· != 1);
- s2460RootCycleType_factorDegrees (sigma) (H explicit S2440 action):
    rootCycleType K L f hsplit sigma = factorDegrees.filter (· != 1).

The explicit H binder uses
  S2440RootPermCycleCleanActual.instMulSemiringActionAlgEquivRingOfIntegers_tmp K L
  S2440RootPermCycleCleanActual.instSMulCommClassAlgEquivRingOfIntegers_tmp K L
and the cycleType in the proof is written with the explicit
  S2440RootPermCycleCleanActual.instDecidableEqElemQuotientRingOfIntegersIdealRootSetFbar
using convert (Subsingleton proof-irrelevance).

## Exact first missing: corrected theorem with arithFrobAt

S2167FrobeniusExists produces H under the ambient/global
RingOfIntegers.instMulSemiringAction, while s2460RootCycleType_factorDegrees
needs H under the S2440 local action instance.  The two MulSemiringAction
structures are not definitionally equal (rfl fails), so H cannot be fed
directly.

Need one of:
1. an instance-transport lemma moving IsArithFrobAt from the global action to
   the S2440 action (their smul on O_L is the same restricted Galois action,
   but the structures are not defeq);
2. restate S2167FrobeniusExists under the S2440 explicit action;
3. state the corrected theorem directly with the explicit S2440 H and
   separately prove the S2217 DedekindFrobeniusCycleTypeStatementCorrected
   instance bridge.

Then orbitSizeMultiset follows by adding fixed points/1s.

## Status

- rootCycleType equality is actual.
- corrected theorem NOT accepted.
- no fake; S2427 sorryAx unused.
