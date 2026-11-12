# S2207: transfer naturality exact surface

Layer: O (transfer naturality).
Source object: verlagerungOpen, Abelianization.map, S2200ConjEquiv.
Domain: transfer under conjugation.
Direction: exact missing naturality; Mathlib transfer API lacks it.

BUILT:
- S2207TransferNaturalityRequired = S2200TransferNaturalityRequired.
- S2207TransferDefNaturalityInput: explicit transfer-def/product-formula naturality target.
- S2207TransferCompatRequired, S2207MuQZMulAutRequired.

MISSING exact: conjugation naturality of MonoidHom.transfer/verlagerungOpen. transfer_def and product formula are available but no naturality lemma; no fake proof.

Lean: tmp/sheaf/xif/paper/S2207TransferNaturalityProofActual.lean
EXIT=0; SHA256 113C17968DADF68FBE310AFFE602CF5D3EAB71EBA6F8D03521CCC4756950BE9C
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2207TransferNaturalityProofActual.olean
olean SHA256: BBFB30FF6A18CDD111D5B43FD77CFD5246B91598413547BBB646FBCF3E380A20
axioms: none (definitions/Prop surface only; no theorem closure).