import tmp.sheaf.xif.paper.S1878CoherentAffineBridgeActual
import tmp.sheaf.xif.paper.S1814OrbicurveCoversAffineActual
import tmp.sheaf.xif.paper.S1779CorrectFiniteEtaleTargetActual
import tmp.sheaf.xif.paper.S1833ActualCoverCoproductsActual

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
open LeanFormal.IUT.XiFPaper.S1833ActualCoverCoproductsActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1878CoherentAffineBridgeActual

/-- Essential surjectivity of the coherent subcategory of the weak cover
category. -/
def S1865CoherentEssSurj : Prop :=
  ∀ A : S1728Cover, ∃ C : S1878CoherentCategory, Nonempty (S1878Underlying C ≅ A)

/-- The whole weak cover category is equivalent to the affine target, from the
coherent affine equivalence and essential surjectivity of the coherent
subcategory. -/
theorem S1865WeakEquivTarget
    (h : S1878Full ∧ S1878EssSurj) (hE : S1865CoherentEssSurj) :
    Nonempty (S1728Cover ≌ S1878Target) := by
  letI : S1878Functor.IsEquivalence := S1878Functor_isEquivalence_iff_full_essSurj.mpr h
  let F := inducedFunctor (F := CoherentCover.cover)
  letI : F.EssSurj := ⟨fun A => hE A⟩
  letI : F.IsEquivalence :=
    { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  exact ⟨F.asEquivalence.symm.trans S1878Functor.asEquivalence⟩

/-- Hence the actual weak cover category is equivalent to the finite-etale
algebra side. -/
theorem S1865WeakAlgEquiv
    (h : S1878Full ∧ S1878EssSurj) (hE : S1865CoherentEssSurj) :
    Nonempty (S1728Cover ≌ S1779AlgR) := by
  obtain ⟨e⟩ := S1865WeakEquivTarget h hE
  exact ⟨e.trans S1814AlgEquiv.symm⟩

/-- Consequently S1833's exact first missing holds. -/
theorem S1865S1833FirstMissing
    (h : S1878Full ∧ S1878EssSurj) (hE : S1865CoherentEssSurj) :
    S1833FirstMissing :=
  S1833FirstMissing_iff.mpr (S1865WeakAlgEquiv h hE)

end LeanFormal.IUT.XiFPaper.S1865CoprodApexActual
