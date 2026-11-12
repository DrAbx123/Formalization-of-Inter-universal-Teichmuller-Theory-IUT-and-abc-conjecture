# S2189: transfer compatibility and conditional muQZ endomorphism

Layer: O (muQZ conjugation).
Source object: Stage transfer, conjugation, muQZ colimit.
Domain: transfer compatibility and colimit additive endomorphism.
Direction: conditional actual additive endomorphism from transfer compatibility; full MulAut action exact missing.

BUILT:
- S2189TransferCompatibilityRequired = S2179TransferCompatible.
- S2189MuQZEndOfTransfer: conditional actual additive endomorphism muQZ ->+ muQZ from transfer compatibility, via muQZ_lift.
- S2189MuQZMulAutData/Required: exact full MulAut action data surface.

MISSING exact: S2179TransferCompatible proof; inverse/group-law/continuity for a full MulAut action. No fake.

Lean: tmp/sheaf/xif/paper/S2189TransferCompatActual.lean
EXIT=0; SHA256 FBA01E1D3936E0FA60F4E88253604985FBA6CDD8A5D652236E803490167B344D
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2189TransferCompatActual.olean
olean SHA256: 60827ADDF6056784911C4F126D480C3F080917D8DCE683098EF2049D1481958A
axioms: propext, Classical.choice, Quot.sound (no sorryAx).