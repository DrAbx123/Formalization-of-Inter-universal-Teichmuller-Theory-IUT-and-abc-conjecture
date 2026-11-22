/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1S1915DegreeFinrankActual
import tmp.sheaf.xif.paper.Mzk1C3S1902BallMassFormulaActual
import tmp.sheaf.xif.paper.Mzk1S1915ComparisonActual
import tmp.sheaf.xif.paper.Mzk1RootImageRadiusFormulaActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import Mathlib.Tactic

/-! # GAP-P7-BALL-MASS (A5): normalized hull log = 1 - sum d_b c_b/(2l) log p_b -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1C3S1902NormalizedLogActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S709RootImageRadiusFormulaActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1S1915DegreeFinrankActual
open LeanFormal.IUT.XiFPaper.Mzk1S1915ComparisonActual
open MeasureTheory
open scoped ENNReal BigOperators NNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **(A5)** The S1915 closed form in the paper-normalized shape
`1 - Σ_b d_b · c_b/(2l) · log p_b`. -/
theorem s1915ClosedForm_eq_one_sub_sum :
    s1915ClosedForm T =
      1 - ∑ b : Bad (nativePlaceSelection T),
        (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : ℝ) *
          (qVFamNormalizedCoefficient T b / (2 * (l.value : ℝ))) *
            Real.log (qVFamTensorP T b : ℝ) := by
  unfold s1915ClosedForm
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [s1915LocalDegree_eq_finrank T b, rootImageRadius_eq_p_rpow]
  have hlog : Real.log ((qVFamTensorP T b : ℝ).rpow
      (-(qVFamNormalizedCoefficient T b) / (2 * (l.value : ℝ)))) =
      (-(qVFamNormalizedCoefficient T b) / (2 * (l.value : ℝ))) *
        Real.log (qVFamTensorP T b : ℝ) :=
    Real.log_rpow (by
      exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos) _
  rw [hlog]
  ring
/-- **(A5)** The actual normalized hull log-volume (S1902 normalization). -/
theorem log_normalized_hull_eq_one_sub_sum :
    Real.log (s1902NormalizedHaar T (s1902Hull T)).toReal =
      1 - ∑ b : Bad (nativePlaceSelection T),
        (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : ℝ) *
          (qVFamNormalizedCoefficient T b / (2 * (l.value : ℝ))) *
            Real.log (qVFamTensorP T b : ℝ) :=
  (s1915_log_normalized_hull T).trans (s1915ClosedForm_eq_one_sub_sum T)

end LeanFormal.IUT.XiFPaper.Mzk1C3S1902NormalizedLogActual