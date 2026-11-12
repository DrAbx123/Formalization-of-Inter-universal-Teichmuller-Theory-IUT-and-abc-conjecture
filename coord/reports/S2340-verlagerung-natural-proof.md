# S2340: naturality composition exact surface

Layer: O (transfer compatibility).
Source object: S2300VerlagerungNaturalRequired.
Domain: composition of verlagerungOpen equivalence.
Direction: exact surface; S2336/S2338 actual inputs.

BUILT:
- S2340VerlagerungNaturalRequired = S2300VerlagerungNaturalRequired.
- S2340StageCompatibleRequired = S2179TransferCompatible.

MISSING exact: Ab.map inclusion/equivMap compatibility, i.e. lifting S2317_subgroupOf_map from subgroups to Abelianization maps, to combine S2336_verlagerungOpen_eq + S2292_transferAb_natural. No fake.

Lean: tmp/sheaf/xif/paper/S2340VerlagerungNaturalProofActual.lean
EXIT=0; SHA256 B23E1B71D25A7135EFF33DB744B47C1D6072DE44FE2C2FB321AFD65C10B24CEA
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2340VerlagerungNaturalProofActual.olean
olean SHA256: 15DF4D5A59F3A0AE87E055FA5B5D7B6EBF9794811AC02787A6B2615FD851C1DF
axioms: none (definition/Prop surface only; no theorem closure).