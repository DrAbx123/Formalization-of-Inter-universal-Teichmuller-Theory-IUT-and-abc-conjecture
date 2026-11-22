import tmp.sheaf.xif.paper.S1878CoherentAffineBridgeActual
import tmp.sheaf.xif.paper.S1814OrbicurveCoversAffineActual
import tmp.sheaf.xif.paper.S1779CorrectFiniteEtaleTargetActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1865CoprodApexActual

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1814OrbicurveCoversAffineActual
open LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1878CoherentAffineBridgeActual

theorem S1865TargetHasFiniteCoproducts : HasFiniteCoproducts S1878Target := by
  refine ⟨fun n => ?_⟩
  exact @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    S1878Target _ S1779AlgR _ (Discrete (Fin n)) _
    S1814AlgEquiv.symm.functor
    S1814AlgEquiv.symm.isEquivalence_functor
    (inferInstance : HasColimitsOfShape (Discrete (Fin n)) S1779AlgR)

theorem S1865CoherentHasFiniteCoproducts
    (h : S1878Full ∧ S1878EssSurj) :
    @HasFiniteCoproducts S1878CoherentCategory inferInstance := by
  letI : S1878Functor.IsEquivalence := S1878Functor_isEquivalence_iff_full_essSurj.mpr h
  refine ⟨fun n => ?_⟩
  exact @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    S1878CoherentCategory _
    S1878Target _
    (Discrete (Fin n)) _
    S1878Functor inferInstance
    (S1865TargetHasFiniteCoproducts.out n)

/-- Essential surjectivity of the coherent subcategory of the weak cover
category: every weak cover is isomorphic to the underlying cover of a coherent
one. -/
def S1865CoherentEssSurj : Prop :=
  ∀ A : S1728Cover, ∃ C : S1878CoherentCategory, Nonempty (S1878Underlying C ≅ A)

theorem S1865WeakHasFiniteCoproducts
    (h : S1878Full ∧ S1878EssSurj) (hE : S1865CoherentEssSurj) :
    HasFiniteCoproducts S1728Cover := by
  haveI := S1865CoherentHasFiniteCoproducts h
  let F := inducedFunctor (F := CoherentCover.cover)
  letI : F.EssSurj := ⟨fun A => hE A⟩
  letI : F.IsEquivalence :=
    { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  refine ⟨fun n => ?_⟩
  exact @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    S1728Cover _ S1878CoherentCategory _ (Discrete (Fin n)) _
    F.asEquivalence.inverse
    (Equivalence.isEquivalence_inverse F.asEquivalence)
    (inferInstance : HasColimitsOfShape (Discrete (Fin n)) S1878CoherentCategory)

end LeanFormal.IUT.XiFPaper.S1865CoprodApexActual
