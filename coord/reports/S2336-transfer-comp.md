# S2336: transfer comp and verlagerungOpen_eq SUCCESS

Layer: O (transfer compatibility).
Source object: MonoidHom.transfer, Abelianization.map, verlagerungOpen.
Domain: transfer composition and subgroup transfer.
Direction: PROVED transfer_comp and verlagerungOpen_eq.

BUILT:
- S2336_transfer_comp: ψ (transfer ϕ g) = transfer (ψ.comp ϕ) g, via transfer_def and S2292_map_diff.
- S2336_verlagerungOpen_eq: verlagerungOpen h = (Ab.map e).comp (transferAb (H.subgroupOf K)), with explicit H.FiniteIndex.

PROVED: both; axioms propext, Classical.choice, Quot.sound.

NEXT: combine S2292_transferAb_natural + S2317_subgroupOf_map to get S2300VerlagerungNaturalRequired, then S2179/toStage.

Lean: tmp/sheaf/xif/paper/S2336TransferCompActual.lean
EXIT=0; SHA256 A3A5AA1C053A2C98A64623B5E5B4B8F0889F8145B9AC142955EA90CC2F64CAD3
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2336TransferCompActual.olean
olean SHA256: 5C1B6FBC9C299DC355658B2EC6764AFDDFE85BFB8156BD3B2B545BB5C727ABF5
axioms: propext, Classical.choice, Quot.sound (no sorryAx).