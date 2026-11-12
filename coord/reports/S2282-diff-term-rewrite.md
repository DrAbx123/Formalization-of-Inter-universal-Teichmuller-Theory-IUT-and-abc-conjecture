# S2282: actual generic diff transport and S2226 closure

Layer: O (diff/transfer product).
Source object: generic group equivalence, transported transversals, explicit diff product.
Domain: diff product invariance.
Direction: PROVED generic diff transport; S2226DiffTransportRequired inhabited.

BUILT:
- S2282_term_eq: per-term rewrite via Subtype.ext/hsub and hϕ.
- S2282_diff_explicit_transport: explicit product equality via Finset.prod_bij.
- S2282_diff_transport: diff ϕ' (transport S) (transport T) = diff ϕ S T.
- S2282_diff_transport_required: inhabits S2226DiffTransportRequired.

PROVED: generic diff transport; axioms propext, Classical.choice, Quot.sound; no sorryAx.

NEXT: specialize to verlagerungOpen/toStage, giving S2179TransferCompatible; then colimit descent and MulAut action.

Lean: tmp/sheaf/xif/paper/S2282DiffTermRewriteActual.lean
EXIT=0; SHA256 1777A290ABB4266A5A7762C7F56331DD606DAD6C3BF016BE4664B22D99DF726D
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2282DiffTermRewriteActual.olean
olean SHA256: 8A362BFDEABCFA993CEA234B9683648FDD52EAD6EE6AC7E220A5998AEFB29DD8
axioms: propext, Classical.choice, Quot.sound (no sorryAx).