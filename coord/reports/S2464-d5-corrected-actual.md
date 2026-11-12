# S2464: corrected Dedekind-Frobenius theorem actual

Date: 2026-11-03. Serial -j1.

## Actual

tmp/sheaf/xif/paper/S2464D5CorrectedActual.lean
  SHA256 FE9CE3F38378DD62A662BFD56F970BB432F9541CA9E89F3BC0E431740BA58C13
  EXIT=0
  olean SHA256 93E324627D604D02ABCCB2053B8215043A3E923D25261162DC9D9ADCAD739A6F
  size 79336
  axioms propext, Classical.choice, Quot.sound; no sorryAx.

Theorem s2464CorrectedCycleType:
  DedekindFrobeniusCycleTypeStatementCorrected K L f p P hmonic hsep hsplit.

Proof:
- S2167FrobeniusExists gives sigma and global IsArithFrobAt Hglobal;
- S2463 action transport (s2463_smul_eq / s2463_toAlgHom_eq) converts Hglobal
  to the S2440 local action H2440;
- s2460RootCycleType_factorDegrees gives
    rootCycleType K L f hsplit sigma = factorDegrees.filter (· != 1);
- exact existential.

## Orbit-size: exact remaining

Need DedekindFrobeniusOrbitSizeStatement:
  orbitSizeMultiset (rootPerm ... sigma) = factorDegrees (fbar f p).

Available: rootCycleType equality; Equiv.Perm.card_fixedPoints:
  card fixedPoints = card roots - cycleType.sum.
Need the multiset arithmetic:
  factorDegrees = factorDegrees.filter (· != 1) + replicate (count 1) 1
and card roots L = factorDegrees.card = factorDegrees.sum = f.natDegree.
Then orbitSizeMultiset = filter != 1 + replicate fixed 1 = factorDegrees.
This arithmetic was not completed in this file.

## Status

- Corrected cycle-type theorem ACTUAL.
- Orbit-size theorem missing (exact arithmetic above).
- No fake; S2427 sorryAx unused.
