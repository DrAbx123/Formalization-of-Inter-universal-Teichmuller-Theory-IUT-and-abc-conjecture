import tmp.sheaf.xif.paper.S2058D6FiniteEtaleActual

/-! # S2629: field-generic cancellation interfaces and corrected consumer -/

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual

namespace LeanFormal.IUT.XiFPaper.S2629GenericCancellationFields

universe u

variable {F : Type u} [Field F]

/-- Field-generic right cancellation of 2-isomorphisms under whiskering by y. -/
structure RightCancellationGen
    {Y Z : EtaleStackOverField F} (y : Y.Hom Z) where
  cancelRight : ∀ {P : EtaleStackPseudofunctor F}
    (A B : Pseudofunctor.StrongTrans P Y.fiber),
    Iso (Pseudofunctor.StrongTrans.vcomp A y)
      (Pseudofunctor.StrongTrans.vcomp B y) →
    Iso A B

noncomputable def cancellationOfGen
    {X Y Z : EtaleStackOverField F} (m : X.Hom Y) (y : Y.Hom Z)
    (R : RightCancellationGen y)
    (T : SchemeOverField F)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor F T) Y.fiber)
    (Qx : EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.vcomp m y) T
      (Pseudofunctor.StrongTrans.vcomp ptY y)) :
    Iso (Pseudofunctor.StrongTrans.vcomp Qx.toSource m)
      (Pseudofunctor.StrongTrans.vcomp Qx.projectionMap.transformation ptY) :=
  R.cancelRight
    (Pseudofunctor.StrongTrans.vcomp Qx.toSource m)
    (Pseudofunctor.StrongTrans.vcomp Qx.projectionMap.transformation ptY)
    ((S2058AssociatorIso Qx.toSource m y).trans
      (Qx.commutes.trans
        (S2058AssociatorIso Qx.projectionMap.transformation ptY y).symm))

/-- Field-generic isPullback right-cancellation coherence. -/
structure M1RightCancellationWitnessGen
    {Y Z : EtaleStackOverField F} (y : Y.Hom Z) where
  cancelWitness : ∀ {X : EtaleStackOverField F} (m : X.Hom Y)
    (T : SchemeOverField F)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor F T) Y.fiber)
    (Qx : EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.vcomp m y) T
      (Pseudofunctor.StrongTrans.vcomp ptY y))
    (commutes : Iso (Pseudofunctor.StrongTrans.vcomp Qx.toSource m)
      (Pseudofunctor.StrongTrans.vcomp Qx.projectionMap.transformation ptY)),
    (EtalePseudofunctorSquare.mk
      Qx.toSource Qx.projectionMap.transformation m ptY commutes).TwoPullbackWitness

/-- Field-generic corrected consumer. -/
def BaseChangePresentationFieldWithHypothesesGen (F : Type u) [Field F] : Type (u + 1) :=
  ∀ {X Y Z : EtaleStackOverField F} (m : X.Hom Y) (y : Y.Hom Z)
    (T : SchemeOverField F)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor F T) Y.fiber),
    (Qy : EtaleStackBaseChangePresentation y T
      (Pseudofunctor.StrongTrans.vcomp ptY y)) →
    (Qx : EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.vcomp m y) T
      (Pseudofunctor.StrongTrans.vcomp ptY y)) →
    AlgebraicGeometry.IsFinite Qy.projection.left →
    AlgebraicGeometry.Etale Qy.projection.left →
    AlgebraicGeometry.IsFinite Qx.projection.left →
    AlgebraicGeometry.Etale Qx.projection.left →
    Σ' P : EtaleStackBaseChangePresentation m T ptY,
      AlgebraicGeometry.IsFinite P.projection.left ∧
        AlgebraicGeometry.Etale P.projection.left

noncomputable def fieldWithHypothesesOfCancellationGen
    (cancelCommutes : ∀ {Y Z : EtaleStackOverField F} (y : Y.Hom Z),
      RightCancellationGen y)
    (cancelWitness : ∀ {Y Z : EtaleStackOverField F} (y : Y.Hom Z),
      M1RightCancellationWitnessGen y) :
    BaseChangePresentationFieldWithHypothesesGen F := by
  intro X Y Z m y T ptY Qy Qx hQyF hQyE hQxF hQxE
  let commutes := cancellationOfGen m y (cancelCommutes y) T ptY Qx
  let hpb := (cancelWitness y).cancelWitness m T ptY Qx commutes
  refine ⟨?P, ?_⟩
  · exact
      { pullbackScheme := Qx.pullbackScheme
        projection := Qx.projection
        projectionMap := Qx.projectionMap
        toSource := Qx.toSource
        commutes := commutes
        isPullback := hpb }
  · exact ⟨hQxF, hQxE⟩

#check RightCancellationGen
#check M1RightCancellationWitnessGen
#check fieldWithHypothesesOfCancellationGen
#print axioms fieldWithHypothesesOfCancellationGen

end LeanFormal.IUT.XiFPaper.S2629GenericCancellationFields
end
