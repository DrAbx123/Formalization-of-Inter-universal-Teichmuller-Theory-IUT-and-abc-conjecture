# S2258: diff product final attempt

Layer: O (diff/transfer product).
Source object: diff, transported transversals, S2242 identity.
Domain: diff product reindexing.
Direction: exact missing; minimal failure recorded.

MINIMAL FAILURE:
- After unfolding diff, the product is tied to the local Fintype instance of Quotient (leftRel H).
- Reindexing via Fintype.prod_equiv needs a definitional match between G ⧸ H and G' ⧸ H.map e; Lean reports dependent-instance mismatch and elaborates H.map (↑e) H vs H.map e.toMonoidHom H differently.
- S2258_diff_eq rfl failed on the two Fintype instances; the later rewrite hα also did not find the transported leftQuotientEquiv pattern under the explicit S2258DiffTerm.

BUILT:
- S2258DiffInvarianceRequired = S2226DiffTransportRequired.

MISSING exact: a local-instance-independent explicit diff product definition and its Fintype.prod_equiv reindex proof. S2242 identity and S2233 reindex remain actual. No fake.

Lean: tmp/sheaf/xif/paper/S2258DiffProductFinalActual.lean
EXIT=0; SHA256 F1C0D6D1DC7252F796501F458C5019A73E890550ED6F86A6B2D4AC1ABF1B21CC
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2258DiffProductFinalActual.olean
olean SHA256: 57FBEA79B17802BE7020B88C1D1B691C4FFF696D69E4D446A83BB6DADCBFAE38
axioms: none (definition/Prop surface only; no theorem closure).