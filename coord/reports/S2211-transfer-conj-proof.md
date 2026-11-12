# S2211: transfer naturality transversal API surface

Layer: O (transfer naturality).
Source object: LeftTransversal, MonoidHom.transfer, verlagerungOpen.
Domain: transfer under conjugation.
Direction: explicit transversal attempt; transport API exact missing.

BUILT:
- S2211TransferNaturalityRequired = S2207TransferNaturalityRequired.
- S2211ConjugatedTransversalTransportRequired: exact transport property for LeftTransversal under group isomorphism.
- S2211OpenSubgroupTransversalTransportRequired: concrete open-subgroup version.

MISSING exact: Mathlib Transfer.lean provides diff/transfer_def/product formula but no map/transport of LeftTransversal along a group isomorphism/conjugation; without that API the transfer product invariance cannot be stated/proved. No fake.

Lean: tmp/sheaf/xif/paper/S2211TransferConjProofActual.lean
EXIT=0; SHA256 31DC7DF481956109077CE849B46B18EF5C3A45FC152A1A743809CB5F88823BC8
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2211TransferConjProofActual.olean
olean SHA256: 100208638069658A4AC36950017130E2958A67CA8C3BF992DB56EA9EAC2BCFF6
axioms: none (definitions/Prop surface only; no theorem closure).