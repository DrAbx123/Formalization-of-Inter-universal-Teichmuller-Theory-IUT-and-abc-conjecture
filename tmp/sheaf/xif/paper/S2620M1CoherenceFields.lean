import tmp.sheaf.xif.paper.S2619RightCancellationActual
import tmp.sheaf.xif.paper.S2096StackMorphismActual

/-! # S2620: M1 new coherence fields and corrected consumer -/

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2618M1CancellationGoal
open LeanFormal.IUT.XiFPaper.S2619RightCancellationActual
open LeanFormal.IUT.XiFPaper.S2096StackMorphismActual

namespace LeanFormal.IUT.XiFPaper.S2620M1CoherenceFields

universe u

/-- New coherence: the isPullback witness of the `m`-square at `ptY`, obtained
from the `(m ; y)`-square witness by right cancellation of `y`. -/
structure M1RightCancellationWitness
    {Y Z : EtaleStackOverField S1726K} (y : Y.Hom Z) : Type 1 where
  cancelWitness : ∀ {X : EtaleStackOverField S1726K} (m : X.Hom Y)
    (T : SchemeOverField S1726K)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber)
    (Qx : EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.vcomp m y) T
      (Pseudofunctor.StrongTrans.vcomp ptY y))
    (commutes : Iso (Pseudofunctor.StrongTrans.vcomp Qx.toSource m)
      (Pseudofunctor.StrongTrans.vcomp Qx.projectionMap.transformation ptY)),
    (EtalePseudofunctorSquare.mk
      Qx.toSource Qx.projectionMap.transformation m ptY commutes).TwoPullbackWitness

noncomputable def m1CancellationWitnessOf
    (R : ∀ {Y Z : EtaleStackOverField S1726K} (y : Y.Hom Z),
      M1RightCancellationWitness y) :
    M1CancellationWitnessGoal :=
  fun {X Y Z} (m : X.Hom Y) (y : Y.Hom Z) (T : SchemeOverField S1726K)
      (ptY : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber)
      (Qx : EtaleStackBaseChangePresentation
        (Pseudofunctor.StrongTrans.vcomp m y) T
        (Pseudofunctor.StrongTrans.vcomp ptY y))
      (commutes : Iso (Pseudofunctor.StrongTrans.vcomp Qx.toSource m)
        (Pseudofunctor.StrongTrans.vcomp Qx.projectionMap.transformation ptY)) =>
    (R y).cancelWitness (X := X) m T ptY Qx commutes

/-- Corrected consumer: finite-etale hypotheses are carried on the two input
presentations, not dropped. -/
def BaseChangePresentationFieldWithHypotheses : Type 1 :=
  ∀ {X Y Z : EtaleStackOverField S1726K} (m : X.Hom Y) (y : Y.Hom Z)
    (T : SchemeOverField S1726K)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber),
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

#check M1RightCancellationWitness
#check m1CancellationWitnessOf
#check BaseChangePresentationFieldWithHypotheses

end LeanFormal.IUT.XiFPaper.S2620M1CoherenceFields
end
