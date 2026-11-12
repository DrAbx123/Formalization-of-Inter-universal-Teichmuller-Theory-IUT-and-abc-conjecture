# S2410: internal/external H^1 equivalence and finiteness of the actual H^1

Date: 2026-11-02. Layer O. Consumer: S2384 / S2214 / S2204 / S2114.

## File

tmp/sheaf/xif/paper/S2410H1EquivDoneActual.lean
Source SHA256 8f4a6f50c49bd33b8f0af1badcb45ebb3fc9d983bbcb0a1f89e2815b62bf1f7e
olean SHA256 ab1f39cfd73c202d8a1169a67603ddb2c0ea29f2ee3de7d7b98d176f9eb5df5f
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Built

S2410ToInternal: the reverse quotient map from external ContH1 to the internal
H1, defined by Quotient.lift; welldefinedness uses
QuotientGroup.leftRel_apply, ContH1.mem_coboundaries_iff, the inverse of the
coboundary subgroup, and S2407ExternalCoboundary_to_Cohomologous.
S2410H1Equiv: S2204H1 p n ~ ContH1 (LocalAbsoluteGalois p) (S2145Coeff p n).
S2410H1Comparison: the S2384H1Comparison inhabitant.
S2410FiniteH1: Finite (S2204H1 p n), via S2384FiniteH1OfComparison.

## Remaining exact missing

1. Surjectivity of S2214H1PushforwardHom (the level transition
   H1(n+1) ->* H1(n)); the finite input is now actual, so
   S2214H1RemainingData only needs proj_surjective.
2. lim1 H1 = 0 / S2114CompatibleRepresentativeLift.
3. No unconditional H2 comparison or CoboundaryLift is claimed.
