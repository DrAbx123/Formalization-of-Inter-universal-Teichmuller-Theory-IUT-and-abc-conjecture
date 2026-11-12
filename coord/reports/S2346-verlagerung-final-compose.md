# S2346: final compose exact surface

Layer: O (transfer compatibility).
Source object: S2300VerlagerungNaturalRequired.
Domain: final composition.
Direction: exact surface; subgroupCongr cast issue.

BUILT:
- S2346VerlagerungNaturalRequired = S2300VerlagerungNaturalRequired.
- S2346StageCompatibleRequired = S2179TransferCompatible.

MINIMAL FAILURE:
- S2346_abmap_subgroupCongr aimed at Ab.map subgroupCongr = id, but subgroupCongr maps Ab H to Ab K (different types); cannot equal id on Ab H.
- transferAb_subgroupCongr consequently fails; needs a cast/eqToHom formulation.

MISSING exact: subgroupCongr target cast and final composition. No fake.

Lean: tmp/sheaf/xif/paper/S2346VerlagerungFinalComposeActual.lean
EXIT=0; SHA256 0B202FFB041B366BA15FB24530B57B7EC9AC3F1366E19127BFCBD799E19D4F65
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2346VerlagerungFinalComposeActual.olean
olean SHA256: D6E9403BA83CE3DAEB9BF0B9FB12599F00FBE266495513A7EC8EB007051F69B8
axioms: none (definition/Prop surface only; no theorem closure).