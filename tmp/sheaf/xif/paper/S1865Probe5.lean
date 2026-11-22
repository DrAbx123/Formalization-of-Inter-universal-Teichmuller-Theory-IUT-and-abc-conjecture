import tmp.sheaf.xif.paper.S1865Probe4
import tmp.sheaf.xif.paper.S1865Probe2

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
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
open LeanFormal.IUT.XiFPaper.S1857CoherentLimits01Actual
open LeanFormal.IUT.XiFPaper.S1878CoherentAffineBridgeActual

theorem S1865Coherent11HasFiniteCoproducts
    (h : S1878Full ∧ S1878EssSurj) :
    @HasFiniteCoproducts CoherentCover S1854CoherentCategory11 := by
  haveI := S1865CoherentHasFiniteCoproducts h
  refine ⟨fun n => ?_⟩
  exact @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    CoherentCover S1854CoherentCategory11
    S1878CoherentCategory inferInstance
    (Discrete (Fin n)) _
    S1865CoherentTo1854.asEquivalence.inverse
    (Equivalence.isEquivalence_inverse S1865CoherentTo1854.asEquivalence)
    (inferInstance : HasColimitsOfShape (Discrete (Fin n)) S1878CoherentCategory)

theorem S1865Coherent01HasFiniteCoproducts
    (h : S1878Full ∧ S1878EssSurj) :
    @HasFiniteCoproducts CoherentCover S1854CoherentCategory01 := by
  haveI : @HasFiniteCoproducts CoherentCover S1854CoherentCategory11 :=
    S1865Coherent11HasFiniteCoproducts h
  refine ⟨fun n => ?_⟩
  exact @CategoryTheory.Adjunction.hasColimitsOfShape_of_equivalence
    CoherentCover S1854CoherentCategory01
    CoherentCover S1854CoherentCategory11
    (Discrete (Fin n)) _
    S1857Coherent01To11 S1857Coherent01To11_isEquivalence
    (inferInstance : HasColimitsOfShape (Discrete (Fin n)) CoherentCover)

end LeanFormal.IUT.XiFPaper.S1865CoprodApexActual
