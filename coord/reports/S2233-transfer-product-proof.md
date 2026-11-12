# S2233: actual left-coset quotient reindexing

Layer: O (transfer product).
Source object: Quotient (leftRel H), group equivalence e.
Domain: left cosets.
Direction: actual reindex equivalence; diff product invariance remains missing.

BUILT:
- S2233LeftCosetReindex: Quotient (leftRel H) ≃ Quotient (leftRel (H.map e)).

PROVED: quotient reindex by quotient map + inverse; axioms trio.

MISSING exact: S2226DiffTransportRequired, i.e. diff/transfer product invariance on transported transversals; then verlagerungOpen naturality. No fake.

Lean: tmp/sheaf/xif/paper/S2233TransferProductProofActual.lean
EXIT=0; SHA256 9A15FC6C4FD3C24CBB260A5B6249A3CE0DF0B1BA9C1BDBE054E6B3FD7364674B
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2233TransferProductProofActual.olean
olean SHA256: C268A58BD823D36B89E43FB38858E32CA33BE6DE80E6B4B68D7D8E29E1A48082
axioms: propext, Classical.choice, Quot.sound (no sorryAx).