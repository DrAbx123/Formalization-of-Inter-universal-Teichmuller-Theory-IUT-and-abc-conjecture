# S2273: map bridge actual; transported product reindex still missing

Layer: O (diff/transfer product).
Source object: H.map coercion bridge, explicit diff product.
Domain: diff product reindexing.
Direction: bridge lemma actual; reindex still exact missing.

BUILT:
- S2273_map_bridge: H.map (↑e) = H.map e.toMonoidHom by rfl.
- S2273DiffInvarianceRequired = S2226DiffTransportRequired.

MINIMAL FAILURE:
- Even with S2273_map_bridge, the explicit-product transport theorem still fails: target under instances transparency reports H.map e.toMonoidHom as expected vs H.map (↑e) actual.
- dsimp/tactic context loses the definitional equality; hα/hβ rewrites do not match under the dependent quotient instance.
- The explicit product S2266DiffExplicit and bridge S2273_map_bridge are actual; the blocker is the transitivity/transport elaboration, not the map equality itself.

MISSING exact: transported product reindex. No fake.

Lean: tmp/sheaf/xif/paper/S2273DiffReindexFinalActual.lean
EXIT=0; SHA256 33283D2CA548780C168AB7C6FF69D055E3910BD5B762E3EDDA581E18410E42DE
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2273DiffReindexFinalActual.olean
olean SHA256: AACFAA6A10E223119329FD5C695D6537ABE970843123817FB6EAF7DDDD15925B
axioms: propext, Classical.choice, Quot.sound (no sorryAx).