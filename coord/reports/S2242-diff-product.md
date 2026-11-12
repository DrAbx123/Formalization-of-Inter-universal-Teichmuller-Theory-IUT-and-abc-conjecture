# S2242: actual transported leftQuotientEquiv identity

Layer: O (diff/transfer product).
Source object: S2215TransversalTransport, S2233LeftCosetReindex, leftQuotientEquiv.
Domain: left transversals / diff.
Direction: actual transported representative identity; diff product still missing.

BUILT:
- S2242_transport_leftQuotientEquiv: for transported S and reindexed q, the transported leftQuotientEquiv coercion equals e of the original representative.

PROVED: identity via subtype equality/class equality; axioms trio.

MISSING exact: S2235DiffTransportRequired (diff/product invariance) and verlagerungOpen naturality. No fake.

Lean: tmp/sheaf/xif/paper/S2242DiffProductActual.lean
EXIT=0; SHA256 F4A82BB5C1F66B5712AEA73823BA2EECABEC641E0A19458BCA6EFA3E3934FF8A
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2242DiffProductActual.olean
olean SHA256: 649FDDD81CB502EE88B858F20CAD1025F19B2FCAA3A5FDE420B7A4F88ABD9FA1
axioms: propext, Classical.choice, Quot.sound (no sorryAx).