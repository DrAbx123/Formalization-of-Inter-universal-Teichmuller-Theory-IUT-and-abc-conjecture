# S2338: conjIndex monotonicity actual; naturality exact surface

Layer: O (transfer compatibility).
Source object: S2169ConjIndex, verlagerungOpen.
Domain: conjugation index monotonicity and transfer naturality.
Direction: monotonicity actual; S2300 naturality exact remaining.

BUILT:
- S2338_conjIndex_mono: H ≤ K -> S2169ConjIndex g H ≤ S2169ConjIndex g K.
- S2338VerlagerungNaturalRequired = S2300VerlagerungNaturalRequired.
- S2338StageCompatibleRequired = S2179TransferCompatible.

PROVED: S2338_conjIndex_mono; axioms trio.

MISSING exact: combine S2336_verlagerungOpen_eq + S2292_transferAb_natural + S2317_subgroupOf_map into S2300VerlagerungNaturalRequired. Remaining gap: inclusion/equivMap compatibility of Ab.map(S2200ConjEquiv) with subgroupOfEquivOfLe on abelianizations. No fake.

Lean: tmp/sheaf/xif/paper/S2338TransferCompatDoneActual.lean
EXIT=0; SHA256 1E54F135908121AD2C090B346BA11E8F5897C6085E2D6E796A446E1E93D53DE6
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2338TransferCompatDoneActual.olean
olean SHA256: 2CFAE243ED19DE1A009AEB579D0E23FA9746F56382042EAABD757DE03B2C910C
axioms: propext, Classical.choice, Quot.sound (no sorryAx).