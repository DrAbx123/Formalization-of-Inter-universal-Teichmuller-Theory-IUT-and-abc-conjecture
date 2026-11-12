# S2347: final compose cast exact surface

Layer: O (transfer compatibility).
Source object: S2300VerlagerungNaturalRequired.
Domain: subgroupCongr cast.
Direction: exact surface; cast API still missing.

BUILT:
- S2347VerlagerungNaturalRequired = S2300VerlagerungNaturalRequired.
- S2347StageCompatibleRequired = S2179TransferCompatible.

MINIMAL FAILURE:
- Ab.map (subgroupCongr h) : Ab H -> Ab K, so it cannot be id on Ab H; a cast/eqToHom along congrArg Abelianization h is required.
- transferAb_subgroupCongr must be stated with the casted target; direct equality fails by type.

MISSING exact: eqToHom/cast lemma for Ab.map (subgroupCongr h) and transferAb transport. No fake.

Lean: tmp/sheaf/xif/paper/S2347FinalComposeCastActual.lean
EXIT=0; SHA256 46C121D579C7BA55088C9221BC59734260D4BFC90074DD77C8F8B1250BDC476D
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2347FinalComposeCastActual.olean
olean SHA256: 5974E4716CC9DF71C50CF6C453147DEF281C5006EFFEA133403B94918715ADE1
axioms: none (definition/Prop surface only; no theorem closure).