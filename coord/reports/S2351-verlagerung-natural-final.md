# S2351: final naturality exact surface

Layer: O (transfer compatibility).
Source object: S2300VerlagerungNaturalRequired.
Domain: final composition.
Direction: exact surface; one naturality composition missing.

MINIMAL GOAL after S2336 rewrites and S2341 inclusion:
  (Ab.map eHsub).comp (transferAb Hsub)
    = (transferAb (H'.subgroupOf K')).comp (Ab.map eK)
where eHsub = (equivMapOfInjective Hsub eK).trans (subgroupCongr hcast).
Need combine S2343_transferAb_natural_hom for e0 with S2348_transferAb_subgroupCongr for hcast.

BUILT:
- S2351VerlagerungNaturalRequired = S2300VerlagerungNaturalRequired.
- S2351StageCompatibleRequired = S2179TransferCompatible.

MISSING exact: hnat for eHsub (composition of S2343 and S2348), then final comp_assoc. No fake.

Lean: tmp/sheaf/xif/paper/S2351VerlagerungNaturalFinalActual.lean
EXIT=0; SHA256 87FFF8526F6A7E696B61D7AF75C5ED1325D71ED25E02995234EB371C3EB4C2CF
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2351VerlagerungNaturalFinalActual.olean
olean SHA256: 257CC0F77D6A2D6A191C3152ED1F54E70636EEFA360FE6C24C8E55335213FA00
axioms: none (definition/Prop surface only; no theorem closure).