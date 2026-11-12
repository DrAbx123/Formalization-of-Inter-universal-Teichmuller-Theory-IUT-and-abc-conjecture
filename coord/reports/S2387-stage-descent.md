# S2387: stage descent exact surface

Layer: O (S2179 stage compatibility).
Source object: S2179TransferCompatible.
Domain: toStage/torsion descent.
Direction: exact surface; S2300 naturality actual.

BUILT:
- S2387StageDescentRequired = S2179TransferCompatible.

MINIMAL TARGET: for v : Stage K,
  S2179StageConj g H (toStage h v) = toStage h' (S2179StageConj g K v).
Unfold Stage = Additive (torsion (Ab)), toStage = torsionMap verlagerungOpen,
S2179StageConj = torsionCongr (abelianizationCongr e).
Need pointwise: torsion quotient map commutes with Ab.map e, using S2371_verlagerung_natural.

MISSING exact: stage/torsion pointwise descent. No fake.

Lean: tmp/sheaf/xif/paper/S2387StageDescentActual.lean
EXIT=0; SHA256 08E67929CF72987FD315A423F96FC8F8BC92959AFF63B56440CB887FA5DD47CD
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2387StageDescentActual.olean
olean SHA256: EF35ED857494A209378BCBDE2B7B86F9F9FC5A6ED7C6CDBDB9E8863BD398D9EA
axioms: none (definition/Prop surface only; no theorem closure).