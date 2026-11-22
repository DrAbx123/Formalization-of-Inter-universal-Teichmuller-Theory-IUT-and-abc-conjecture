/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1LocalEstimateGeneralQpilotActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesModelQpilotActual
import Mathlib.Tactic

/-! # Mzk1HeightWeightFromTripleQpilotActual — height-weight bound from triple comparison

A639 (qpilot lane): a single mainline `TripleDependentComparison` (its two fields
quantify over all ε) yields the global height-weight bound shape
`∀ ε>0, ∃ A, ∀ abc, logHeight ≤ (1+ε)·weight + A` via the absorbed estimate and
the reparametrization `δ = min (ε/4) 1`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HeightWeightFromTripleQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1LocalEstimateGeneralQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesModelQpilotActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- Global height-weight bound from a mainline triple-dependent comparison. -/
theorem heightWeightBoundShape_of_tripleComparison
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) :
    HeightWeightBoundShape := by
  intro epsilon hepsilon
  let delta : Real := min (epsilon / 4) 1
  have hdelta_pos : 0 < delta := by
    unfold delta
    exact lt_min (by linarith) (by norm_num)
  have hdelta_le : delta ≤ 1 := by
    unfold delta
    exact min_le_right _ _
  have hdelta_eps : 3 * delta ≤ epsilon := by
    unfold delta
    have hle : min (epsilon / 4) 1 ≤ epsilon / 4 := min_le_left _ _
    linarith
  obtain ⟨D, hD⟩ := height_bound_of_tripleComparison T point C hdelta_pos hdelta_le
  refine ⟨(1 + delta) * ((s1902LogVolume T (s1902Hull T)).toReal + D),
    fun a b c habc => ?_⟩
  have hh := hD a b c habc
  have hw : (0 : Real) ≤ arithmeticWeight (abcRationalPoint a c) :=
    arithmeticWeight_nonneg _
  have hmul : (1 + 3 * delta) * arithmeticWeight (abcRationalPoint a c) ≤
      (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) := by
    nlinarith
  linarith

#check heightWeightBoundShape_of_tripleComparison

end LeanFormal.IUT.XiFPaper.Mzk1HeightWeightFromTripleQpilotActual
end
