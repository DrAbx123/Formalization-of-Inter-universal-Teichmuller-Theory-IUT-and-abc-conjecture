# S2422: stage descent third attempt exact surface

Layer: O (S2179 stage compatibility).
Source object: S2179TransferCompatible.
Domain: Stage/toStage/torsion descent.
Direction: exact surface; direct S2371-to-torsion route still needs coefficient formula.

BUILT:
- S2422StageDescentRequired = S2179TransferCompatible.

MISSING exact: pointwise torsion formula S2179StageConj's abelianization map vs S2200ConjEquiv; then apply S2371_verlagerung_natural on v and lift through CommGroup.torsion/toStage. No fake.

Lean: tmp/sheaf/xif/paper/S2422StageDescent3Actual.lean
EXIT=0; SHA256 B24F271FE50400BA040FE254190025E32E7D5F1D6DBF083B1DA19C3FEC1D2065
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2422StageDescent3Actual.olean
olean SHA256: 2981392F9A0AD236285ED6B13A356F56674D2A30E4440AEF5F6F7330172667FB
axioms: none (definition/Prop surface only; no theorem closure).