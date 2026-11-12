# S2277: generic diff-transport exact surface

Layer: O (diff/transfer product).
Source object: generic G,G', H.LeftTransversal, S2215 transport.
Domain: generic diff product reindex.
Direction: standalone generic statement; no proof yet.

BUILT:
- S2277_map_bridge: H.map (↑e) = H.map e.toMonoidHom by rfl.
- S2277DiffTransportGenericRequired: standalone generic exact Prop.

MISSING exact: S2277DiffTransportGenericRequired. Blocker remains dependent quotient/Fintype instance mismatch even in the standalone generic setting; S2266DiffExplicit and S2273/S2277 map bridge are actual. No fake.

Lean: tmp/sheaf/xif/paper/S2277DiffTransportGenericActual.lean
EXIT=0; SHA256 0567DAA026ABE383EC5690629EF7AF04BAEEAF4455BF500ECA9CB6CD6D1E15A4
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2277DiffTransportGenericActual.olean
olean SHA256: 5B154F933D625A91E80351E71E4F2AB56A9DE95C12A287D95A76916227FEA5A1
axioms: propext, Classical.choice, Quot.sound (no sorryAx).