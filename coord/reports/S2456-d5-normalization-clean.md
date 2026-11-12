# S2456: normalization and permBar cycle type actual

Date: 2026-11-03. Serial -j1 compile.

## Actual

tmp/sheaf/xif/paper/S2456D5FinalActual.lean
  SHA256 C5317E23F64974A08E9C804A748C70488AC10418C38A9761C3BFCF4D3E4B79D5
  EXIT=0
  olean SHA256 95817A9DB7BE55A91761110E8D86113EA309279717BA73891DDED89B75B661E1
  size 211984
  axioms propext, Classical.choice, Quot.sound; no sorryAx.

Theorems:
- s2456M_nodup: normalizedFactors Nodup (from hsep.squarefree);
- s2456S_val: (normalizedFactors.toFinset).val = normalizedFactors;
- s2456_normalization:
    (Finset.univ.filter (2 <= natDegree)).val.map natDegree
      = (normalizedFactors.map natDegree).filter (2 <= .);
- s2456PermBar_cycleType:
    (permBar p P).cycleType
      = (normalizedFactors.map natDegree).filter (2 <= .).

## Exact remaining for D5 corrected theorem

1. S2428 bridge:
   instance mismatch for `s2408FiberSet`/`factorDegrees`, specifically the
   DecidableEq instance of the factor subtype; need to align the Fintype/
   DecidableEq used in `s2456_normalization` with S2428's factorDegrees
   multiset, or prove the equality
   (normalizedFactors.map natDegree).filter (2<=)
     = (factorDegrees (fbar f p)).filter (· != 1)
   directly from S2428 after aligning hcard/fibre notation.
2. S2440 instantiation:
   s2440_permBar_cycleType_eq_rootCycleType expects its own local
   MulSemiringAction/DecidableEq instances; the current S2456 local instances
   produce `IsArithFrobAt` with a different instance argument.
   Either use the exact S2440 instance arguments or restate the transfer
   theorem in S2456 with a fresh local instance.
3. sigma := arithFrobAt, corrected theorem/orbitSize.

## Status

- D5 corrected theorem NOT accepted.
- Single normalization is now actual.
- S2427 sorryAx unused; no fake.
