import tmp.sheaf.xif.paper.S1865CoprodApexActual

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

theorem S1865HasInitial_of_hasFiniteCoproducts
    {C : Type*} [Category C] [HasFiniteCoproducts C] : HasInitial C := by
  let F : Discrete (Fin 0) ⥤ C := functorOfIsEmpty _ _
  haveI : HasColimit F := (HasFiniteCoproducts.out 0).has_colimit F
  have hinit : IsInitial (colimit F) :=
    (isColimitEquivIsInitialOfIsEmpty (C := C) (J := Discrete (Fin 0)) (F := F)
      (colimit.cocone F)).toFun (colimit.isColimit F)
  exact IsInitial.hasInitial hinit

theorem S1865CoherentHasInitial (h : S1878Full ∧ S1878EssSurj) :
    @HasInitial S1878CoherentCategory inferInstance := by
  letI := S1865CoherentHasFiniteCoproducts h
  exact S1865HasInitial_of_hasFiniteCoproducts

end LeanFormal.IUT.XiFPaper.S1865CoprodApexActual
