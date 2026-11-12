# S2348: transferAb subgroupCongr by cases SUCCESS

Layer: O (transfer compatibility).
Source object: transferAb under subgroupCongr equality.
Domain: subgroup equality cast.
Direction: PROVED transferAb_subgroupCongr by cases h.

BUILT:
- S2348_transferAb_subgroupCongr: (Ab.map (subgroupCongr h)).comp (transferAb H) = transferAb K.
Proof: cases h; rewrite subgroupCongr rfl to MulEquiv.refl; simp.

PROVED: cast lemma; axioms trio.

NEXT: use cases/subst on hcast in final compose to close S2300VerlagerungNaturalRequired.

Lean: tmp/sheaf/xif/paper/S2348CastByCasesActual.lean
EXIT=0; SHA256 00DB8308546B1A9C2688B6E5983980824A65C7C878CD5B15290D4936760F4A4E
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2348CastByCasesActual.olean
olean SHA256: B111F312D735224AC7908228319AD584873D3292EFC94C0D472A1DC9433AD2C2
axioms: propext, Classical.choice, Quot.sound (no sorryAx).