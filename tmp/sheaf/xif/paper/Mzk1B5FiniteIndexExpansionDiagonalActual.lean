/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5FiniteIndexExpansionIffActual
import tmp.sheaf.xif.paper.Mzk1B5HproductDiagonalActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexExpansionDiagonalActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.PaperOModuleActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineFromBadPrimeSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1B5AssemblyNoHproductAttemptActual
open LeanFormal.IUT.XiFPaper.Mzk1B5HproductGeneralAttemptActual
open LeanFormal.IUT.XiFPaper.Mzk1B5HproductDiagonalActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLineConstructionActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem finiteIndexExpansion_diagonal
    (s : Finset (NumberField.FinitePlace T.arithmetic.K))
    (dH : ∀ v, PaperOModuleActual.LocalField (k := T.arithmetic.K) v)
    (hH : (badPrimeSource T).qPilotLineBundle ≠ 0) :
    FiniteIndexExpansion T (badPrimeSource T).qPilotLineBundle s dH dH := by
  unfold FiniteIndexExpansion
  have hrel : relativeDetLog (k := T.arithmetic.K)
      (badPrimeSource T).qPilotLineBundle (badPrimeSource T).qPilotLineBundle = 0 := by
    unfold relativeDetLog
    have hone : relativeDetLine (k := T.arithmetic.K)
        (badPrimeSource T).qPilotLineBundle (badPrimeSource T).qPilotLineBundle = 1 := by
      unfold relativeDetLine
      rw [determinantLine_eq, determinantLine_eq, mul_inv_cancel₀ hH]
    rw [hone, globalLogVolume_one]
  have hfin : finiteIndexContribution T (badPrimeSource T).qPilotLineBundle
      (badPrimeSource T).qPilotLineBundle s dH dH = 0 := by
    unfold finiteIndexContribution
    simp
  rw [hrel, hfin]
end LeanFormal.IUT.XiFPaper.Mzk1B5FiniteIndexExpansionDiagonalActual
