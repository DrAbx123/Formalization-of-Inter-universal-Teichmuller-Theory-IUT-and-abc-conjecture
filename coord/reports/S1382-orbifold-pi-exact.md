# S1382: D6 orbifold Pi exact first field

Date: 2026-10-30
Lean: tmp/sheaf/xif/paper/S1382OrbifoldPiActual.lean
EXIT=0; SHA256 FC186383242D8F03C786EA0362A2595763472E89872FB47F4C3D7BF65CCD945B.

## Read/actual donors

S1348D6OrbicurveActual: actual Gaussian curve/coordinate ring, actual finite
etale double cover R ⊗_K (K x K), actual structure group with nontrivial
sheet swap, actual once-punctured cusp count, actual cover surjectivity.

S1319OrbicurveClauseActual: actual point-level D6 boundary clause; exact
S1319OrbifoldPiGap.

S1359OrbifoldPiActual: first field S1359FirstField (nonterminal hyperbolic
orbicurve over K, once-punctured signature), residual group data
OrbicurveFundamentalGroupData F.X G_K, equivalence S1359OrbifoldPiDataEquiv.

## Exact first field

S1382OrbifoldPiExactFirstField l :=
  Sigma F : S1359FirstField l, S1359OrbifoldPiRemainder l F.

Actual equivalence: s1382EquivData : exact field ≃ S1319OrbifoldPiData l.
Actual characterization: Nonempty exact field ↔ S1319OrbifoldPiGap l.
No inhabitant is asserted.

## Why not actual X/group data

The tree has no non-point etale stack fiber (MissingD6GeometricRealization)
and no OrbicurveEtaleFundamentalGroup/OrbicurveFundamentalGroupData inhabitant.
S1319/S1348 actual data gives curve/cover/cusp, but not the stack orbicurve or
the certified group data.

No terminal/point fiber, no l-torsion sequence, no connected-cover
construction is used.
