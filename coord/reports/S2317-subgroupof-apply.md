# S2317: apply formula and subgroupOf map SUCCESS

Layer: O (verlagerungOpen naturality coercion).
Source object: S2200ConjEquiv, subgroupOf.
Domain: conjugation equivalence coercion.
Direction: PROVED apply formula and S2300SubgroupOfMapRequired.

BUILT:
- S2317ConjEquiv_apply: (S2200ConjEquiv p g H x : Gv) = g⁻¹ * x * g.
- S2317_subgroupOf_map: S2300SubgroupOfMapRequired, proved via Subgroup.ext, S2311 comap bridge, apply formula, and symm formula by group.

PROVED: apply formula and subgroupOf map; axioms propext, Classical.choice, Quot.sound.

NEXT: use S2317_subgroupOf_map in S2300VerlagerungNaturalRequired, then S2179TransferCompatible.

Lean: tmp/sheaf/xif/paper/S2317SubgroupOfApplyActual.lean
EXIT=0; SHA256 A5E56771A9F1F2D87CB201878053FA03F5DA288E36B1FAF736C66B28015213D4
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2317SubgroupOfApplyActual.olean
olean SHA256: 2F6FE823D7BA8A2AD727E599DF6B9CBE1687961F99EB7CCB29594E8C3153A11F
axioms: propext, Classical.choice, Quot.sound (no sorryAx).