# S2430: S2179TransferCompatible PROVED (torsion descent)

Layer: O (S2179 stage compatibility).
Source object: S2179TransferCompatible.
Domain: Stage/toStage/torsion descent.
Direction: PROVED.

BUILT:
- S2430_cast_equiv_eq_trans: (h ▸ e) = e.trans (subgroupCongr h).
- S2430_torsionCongr_coe: ((torsionCongr e) w : B) = e (w:A).
- S2430_torsionMap_coe: ((torsionMap f) w : B) = f (w:A).
- S2430_toStage_apply: toStage h (ofMul w) = ofMul (torsionMap (verlagerungOpen h) w).
- S2430_stageConj_eq: S2179StageConj = torsionCongr(abelianizationCongr(S2200ConjEquiv)).
- S2430_stageConj_apply pointwise.
- S2430_transferCompatible : S2179TransferCompatible.
- S2430_stageDescentRequired : S2422StageDescentRequired.

EXIT=0; axioms propext, Classical.choice, Quot.sound; no sorryAx.

SHA256: E9BB85FFB7ED00369423338F9A750105E40CF5DF5319AA8DEC831C5EE2B8F691
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2430TorsionDescentSubagentActual.olean
olean SHA256: E62865A5EFE58B4121DB8EE82BA6A571CF95C1AF94105F4284ACE0FD75A3615C

Status: S2300VerlagerungNaturalRequired (S2371) and S2179TransferCompatible (S2430) CLOSED.
Next: S2189MuQZMulAutData subagent B pending.