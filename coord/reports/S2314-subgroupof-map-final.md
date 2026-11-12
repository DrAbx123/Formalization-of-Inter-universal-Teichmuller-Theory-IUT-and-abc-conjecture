# S2314: subgroupOf map final exact surface

Layer: O (verlagerungOpen naturality coercion).
Source object: S2300SubgroupOfMapRequired.
Domain: subgroupOf/conjugation equivalence.
Direction: exact missing; bridge actual.

MINIMAL FAILURE:
- S2311_mem_comap_toSubgroup expects OpenSubgroup H, while the target uses H.toSubgroup.comap; need H (open) variant alignment.
- Subgroup.mem_subgroupOf.mp hy needs explicit H/K because hy is membership in (H').subgroupOf K'.
- S2200ConjEquiv.symm coercion: simp leaves ↑((subgroupMap ...).symm ((subgroupCongr ...).symm y)) = g * ↑y * g⁻¹ unsolved.

BUILT:
- S2314SubgroupOfMapRequired = S2300SubgroupOfMapRequired.
- S2311_mem_comap_toSubgroup actual from prerequisite.

MISSING exact: subgroupOf map equality. No fake.

Lean: tmp/sheaf/xif/paper/S2314SubgroupOfMapFinalActual.lean
EXIT=0; SHA256 4C06888D968FF338E36BF21CC4965FC63B86D5BA34AFFF3D182045896FE18524
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2314SubgroupOfMapFinalActual.olean
olean SHA256: 041552FEAE0A34841E1DC6684159E9EF67329ABCFEDF7866549D9B3FAE1847AB
axioms: none (definition/Prop surface only; no theorem closure).