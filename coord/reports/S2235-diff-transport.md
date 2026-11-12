# S2235: diff transport exact surface

Layer: O (diff/transfer product).
Source object: transported transversal, left quotient reindex.
Domain: diff product invariance.
Direction: exact missing transport-left-quotient identity and diff product; S2233 reindex actual.

BUILT:
- S2235TransportLeftQuotientRequired: exact identity for the transported transversal's leftQuotientEquiv on reindexed classes.
- S2235DiffTransportRequired = S2226DiffTransportRequired.

MISSING exact: S2235TransportLeftQuotientRequired, then diff/product reindexing. No fake.

Lean: tmp/sheaf/xif/paper/S2235DiffTransportActual.lean
EXIT=0; SHA256 6357D4AC17A15309991B8CDAA5FF508569EE4973243C83A9F8C52CDA68FCFB1D
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2235DiffTransportActual.olean
olean SHA256: 30308EF9F92509891749E3BA9DF100D21508708D86D6BD277FE10F4800565274
axioms: none (definitions/Prop surface only; no theorem closure).