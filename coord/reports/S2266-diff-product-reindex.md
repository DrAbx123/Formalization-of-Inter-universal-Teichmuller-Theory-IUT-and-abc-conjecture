# S2266: explicit diff product and remaining reindex gap

Layer: O (diff/transfer product).
Source object: diff, explicit product via S2266DiffTerm.
Domain: diff product reindexing.
Direction: actual diff=explicit-product bridge; transported product reindex still exact missing.

BUILT:
- S2266DiffTerm: explicit coset term.
- S2266DiffExplicit: product ∏ q, ϕ(term q) with explicit Fintype parameter.
- S2266_diff_explicit: diff ϕ S T = S2266DiffExplicit H S T A ϕ; axioms trio.
- S2266DiffInvarianceRequired = S2226DiffTransportRequired (exact remaining Prop).

MINIMAL FAILURE:
- Transport comparison still hits H.map (↑e) H vs H.map e.toMonoidHom H instance mismatch; after dsimp and rw [← hq], the hα/hβ rewrite does not match under the dependent quotient instance.
- Fintype.ofEquiv with S2233LeftCosetReindex registers the target instance, but the term/leftQuotientEquiv rewrite remains blocked.

MISSING exact: S2266DiffInvarianceRequired. No fake.

Lean: tmp/sheaf/xif/paper/S2266DiffProductReindexActual.lean
EXIT=0; SHA256 32912E8328B198485C70B9E2A22418A12B391EFD2A38B0621E43608FE2E5E8ED
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2266DiffProductReindexActual.olean
olean SHA256: 2F2C9C896C960FE67F20E8B86B0CC6820ECFA21BB90BB48CA3737CB8BD273615
axioms: propext, Classical.choice, Quot.sound (no sorryAx).