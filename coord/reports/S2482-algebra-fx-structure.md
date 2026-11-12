# Algebra F[X]-structure on R: actual

## BUILT (EXIT=0)
S2482NormTransportActual.lean:
- S2482BaseMap : F[X] →+* R = S2482CoordRingEquiv ∘ algebraMap_W.
- S2482ModulePolynomial : Module F[X] R via Module.compHom.
- S2482AlgebraPolynomial : Algebra F[X] R via Algebra.ofModule', with
    algebraMap F[X] R r = S2482BaseMap r (S2482_algebraMap_eq).
- S2482LinearMap : W.CoordinateRing →ₗ[F[X]] R, toFun = S2482CoordRingEquiv,
    map_smul' proved from F-linearity and the algebraMap definition.
- S2482LinearEquiv : W.CoordinateRing ≃ₗ[F[X]] R.
- S2482Basis : Module.Basis (Fin 2) F[X] R, obtained by mapping
    CoordinateRing.basis S2482W along S2482LinearEquiv.
- S2482CoordRingEquiv_algebraMap : e is F[X]-linear on algebraMap.
Axioms: propext, Classical.choice, Quot.sound; no sorryAx.

## Next
Transport CoordinateRing.norm_smul_basis/degree_norm_smul_basis to R using S2482Basis and
S2482CoordRingEquiv; then prove the order-two automorphism preserves the norm filtration and
derive phi(x)=x / phi(y)=±y.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2482NormTransportActual.lean
EXIT=0; SHA256 2194871B49F283C94BC50B122D3350D33AE4D1B55F811B09F3A4B526A88EABCB
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2482NormTransportActual.olean
olean SHA256: 36E11109810D9A5A488B612FF75951F63C0390D93B7DC0D03B2CADECB1191753
axioms: trio