# S2459: actual orbicurve involution square re-export; diagram remains missing

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL:
- S2459InvolutionSquared := S2482EllipticInvolution_square :
    TwoIso (S2482EllipticInvolution >> S2482EllipticInvolution) (id S2482Orbicurve).
  This is exactly OrbicurveSignAction.inversionSquared.
- S2459DiagramMissing : Prop := Nonempty (Pseudofunctor SignActionIndex (EtaleStackPseudofunctor F)) (statement only).

EXIT=0, olean 17768, SHA256 75ef7cc986031f4a3977836fa9f84f33cd598cc58c6e405743731037e6c1f8cf, axioms propext/Classical.choice/Quot.sound.

The Bicategory instance on EtaleStackPseudofunctor F is scoped: open scoped Pseudofunctor.StrongTrans (Mathlib CategoryTheory.Bicategory.FunctorBicategory.Pseudo).

Diagram NOT constructed. With inversionSquared now available, the remaining work is a pseudofunctor
  diagram : SignActionIndex ->p EtaleStackPseudofunctor F
with obj = Xfiber, map signActionGenerator = S2482EllipticInvolution. Mathlib provides
CategoryTheory.pseudofunctorOfIsLocallyDiscrete requiring obj/map/mapId/mapComp plus associator/left/right unitor coherences. No diagram/cF is claimed.

No fake, no IsStack.