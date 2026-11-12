# S2248: diff invariance exact surface

Layer: O (diff/transfer product).
Source object: diff, transported transversals, S2242 identity.
Domain: diff product reindexing.
Direction: exact missing diff product invariance; S2242 identity actual.

BUILT:
- S2248DiffInvarianceRequired = S2226DiffTransportRequired.

MISSING exact: diff product reindexing/Fintype.prod_equiv step. The naive rewrite hit dependent-instance mismatch between G ⧸ H and G' ⧸ H.map e; S2242 transport identity and S2233 reindex are actual. No fake.

Lean: tmp/sheaf/xif/paper/S2248DiffInvarianceActual.lean
EXIT=0; SHA256 48F9F0EFD81928B315698208A3A54F3C7DAA5A303042D457FF2824FA9C70DE2E
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2248DiffInvarianceActual.olean
olean SHA256: 35045FA7F1AE76B767A8C5B7C7A49F0E55DDA06672291F57B470A81E9A122A0C
axioms: none (definition/Prop surface only; no theorem closure).