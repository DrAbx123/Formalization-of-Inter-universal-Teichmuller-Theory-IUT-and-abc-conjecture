import tmp.sheaf.xif.paper.S2540FullGoalActual
import tmp.sheaf.xif.paper.S2539QuotMapInjectiveInterfaceActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2518InvCoverMapActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.XiFPaper.S2540FullGoalActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2540FullBridgeActual

/-- Quotient-surjectivity of the inverse-functor map. -/
def S2540QuotSurjective : Prop :=
  ∀ {C D : FiniteEtaleCover S2482AffineScheme},
    Function.Surjective (fun f : C ⟶ D =>
      Quot.mk (fun a b : Iut.OrbicurveFiniteEtaleCoverMap
        (S2517InvObj C) (S2517InvObj D) => S1728CoverMapRel a b)
        (S2518InvCoverMap f))

/-- Quotient-surjectivity implies the full-lift statement. -/
theorem S2540FullLift_of_quotSurjective
    (h : S2540QuotSurjective) : S2540FullLift := by
  intro C D hcov
  obtain ⟨f, hf⟩ := h (C := C) (D := D)
    (Quot.mk (fun a b : Iut.OrbicurveFiniteEtaleCoverMap
      (S2517InvObj C) (S2517InvObj D) => S1728CoverMapRel a b) hcov)
  refine ⟨f, ?_⟩
  have aux : ∀ a b : Iut.OrbicurveFiniteEtaleCoverMap
      (S2517InvObj C) (S2517InvObj D),
      Relation.EqvGen (fun f g => S1728CoverMapRel f g) a b →
      S1728CoverMapRel a b := by
    intro a b hgen
    induction hgen with
    | rel x y hr => exact hr
    | refl => exact S1728CoverMapRel_refl _
    | symm x y hxy ih => exact S1728CoverMapRel_symm ih
    | trans x y z h1 h2 ih1 ih2 => exact S1728CoverMapRel_trans ih1 ih2
  exact aux _ _ (Quot.eqvGen_exact hf)

#check S2540QuotSurjective
#check S2540FullLift_of_quotSurjective

end LeanFormal.IUT.XiFPaper.S2540FullBridgeActual
end
