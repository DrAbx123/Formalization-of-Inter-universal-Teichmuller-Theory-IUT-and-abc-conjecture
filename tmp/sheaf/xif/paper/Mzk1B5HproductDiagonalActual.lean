/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual
import tmp.sheaf.xif.paper.Mzk1Ob33ArchMetricActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1B5HproductDiagonalActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.PaperOModuleActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineFromBadPrimeSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1B5AssemblyNoHproductAttemptActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLineConstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33ArchMetricActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem b5ProductFormulaBridge_diagonal
    (s : Finset (NumberField.FinitePlace T.arithmetic.K))
    (dH : ∀ v, PaperOModuleActual.LocalField (k := T.arithmetic.K) v)
    (hH : (badPrimeSource T).qPilotLineBundle ≠ 0) :
    B5ProductFormulaBridge T (badPrimeSource T).qPilotLineBundle s dH dH
      (1 : T.arithmetic.Kˣ) := by
  unfold B5ProductFormulaBridge
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
  have harch : archimedeanContribution T (1 : T.arithmetic.Kˣ) = 0 := by
    unfold archimedeanContribution
    simp [archDetMetricWeight]
  rw [hrel, hfin, harch]
  ring
end LeanFormal.IUT.XiFPaper.Mzk1B5HproductDiagonalActual
