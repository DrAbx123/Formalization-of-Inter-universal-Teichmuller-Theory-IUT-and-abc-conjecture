# S2363: final compose second attempt exact surface

Layer: O (transfer compatibility).
Source object: S2300VerlagerungNaturalRequired.
Domain: final composition.
Direction: exact surface; cases hcast dependent elimination fails.

MINIMAL FAILURE:
- after S2336 rewrites and S2341 inclusion, target reduces to hnat:
  (Ab.map eHsub).comp (transferAb Hsub)
  = (transferAb (H'.subgroupOf K')).comp (Ab.map eK).
- attempt to prove hnat by cases hcast failed: Dependent elimination failed on the let-defined H'/eHsub types.
- rw [hnat] then failed because eHsub occurrence was not matching due associativity/instance transparency.

BUILT:
- S2363VerlagerungNaturalRequired = S2300VerlagerungNaturalRequired.
- S2363StageCompatibleRequired = S2179TransferCompatible.

MISSING exact: hnat for eHsub (S2343 + S2348) without cases on dependent let-types, then comp_assoc. No fake.

Lean: tmp/sheaf/xif/paper/S2363VerlagerungNaturalFinal2Actual.lean
EXIT=0; SHA256 A373A6330005E8DCFDFE1742CF927C92503FDA8E7DFB201CED8F52138C2E9FE2
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2363VerlagerungNaturalFinal2Actual.olean
olean SHA256: C89DAA44E0B4FD08997DF61155B0142A96B6E3AE3B5B739AFBF4E41639BFAB3E
axioms: none (definition/Prop surface only; no theorem closure).