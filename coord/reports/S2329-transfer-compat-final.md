# S2329: verlagerungOpen naturality exact surface

Layer: O (transfer compatibility).
Source object: verlagerungOpen, transferAb, subgroupOf map (S2317 actual).
Domain: specialization of transfer naturality.
Direction: exact missing; S2317 subgroupOf map actual.

BUILT:
- S2329VerlagerungNaturalRequired = S2300VerlagerungNaturalRequired.
- S2329StageCompatibleRequired = S2300StageCompatibleRequired.

MINIMAL FAILURE for verlagerungOpen_eq:
- transferAb in the target needs ((H.subgroupOf K).FiniteIndex), which is not inferred from H.FiniteIndex without a local instance.
- rw [verlagerungOpen, Verlagerung.transferAb] fails on the implicit FiniteIndex/typeclass elaboration.

MISSING exact: verlagerungOpen_eq (with explicit finite-index instance) and then S2300VerlagerungNaturalRequired / S2179. No fake.

Lean: tmp/sheaf/xif/paper/S2329TransferCompatFinalActual.lean
EXIT=0; SHA256 B65776B5ED7486332F56D28B6B6C8BBD555B0B240611E672D901EE6A03CC8377
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2329TransferCompatFinalActual.olean
olean SHA256: E4E0D538198CAE47772B3FFF37401E6F05C19F8E23319584894AA971AB8B701F
axioms: none (definition/Prop surface only; no theorem closure).