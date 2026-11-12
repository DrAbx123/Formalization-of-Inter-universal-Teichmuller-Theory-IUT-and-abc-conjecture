# Underlying compression bridge: actual

## BUILT (EXIT=0)
S2482UnderlyingSquareActual.lean:
  S1742HomOfStrongTrans_vcomp
    (eta : StrongTrans (YS S)(YS T)) (theta : StrongTrans (YS T)(YS U)) :
    S1742HomOfStrongTrans (vcomp eta theta) =
      S1742HomOfStrongTrans eta ≫ S1742HomOfStrongTrans theta.
Proof follows S1755's Cat-level computation: rewrite vcomp.app by rfl, Cat.Hom.comp_obj,
then S1742Key twice and Discrete.ext. Avoids comp_app type mismatch.
Axioms: propext, Classical.choice, Quot.sound; no sorryAx.

## Remaining
- Hom-specific square corollary: annotate eta as StrongTrans at S2482AffineOver to avoid
  Hom alias elaboration; then derive g≫g=1 from square=id iso and S1742HomOfStrongTrans_congr.
- Spec.map_surjective -> phi -> classification -> S2482TwoIso_of_hom_eq.
- corrected Hom field, sign action, cF, cK, epsilon.
No fake.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2482UnderlyingSquareActual.lean
EXIT=0; SHA256 2857964322095475051143C56C391AD09945E1B8EF874E9590FB51D3D0826B17
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2482UnderlyingSquareActual.olean
olean SHA256: 8866A60E2C55F15D192FCDEF3D314040CA8420C5A648C549D08ABA5E8C594AC5
axioms: trio