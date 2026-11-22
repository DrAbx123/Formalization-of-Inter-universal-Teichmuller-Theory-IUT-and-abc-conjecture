/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2RelativeMassActual
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionFieldScalingActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic

/-! # P2: weighted sums (Σ_b d_b log) and their connection to R1.3 -/

/-
| field | value |
|---|---|
| Status | PROVED: `p2RExact = W_λ − W_qhat` with `W_λ = Σ_b d_b log‖λ_b‖`, `W_qhat = Σ_b d_b log‖qhat_b‖`; `W_qhat − W_λ = Σ_b d_b log‖c_b‖`; `c0RemainderV2 = −(2l−1)·W_λ` |
| GAP | connection of these root-side weighted sums to the paper label/procession weighted sum is not constructed |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2WeightedSumActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2RelativeMassActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
open scoped BigOperators ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Weighted sum of the actual lambda log norms. -/
noncomputable def p2WeightedLogLambda : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : Real) *
      Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖

/-- Weighted sum of the actual qhat log norms. -/
noncomputable def p2WeightedLogQhat : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : Real) *
      Real.log ‖c0QHat T b‖

/-- (R1.3) as a difference of weighted sums. -/
theorem p2RExact_eq_weighted_sub :
    p2RExact T = p2WeightedLogLambda T - p2WeightedLogQhat T := by
  unfold p2RExact p2WeightedLogLambda p2WeightedLogQhat
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Weighted difference equals the coefficient log sum. -/
theorem p2WeightedLogQhat_sub_lambda_eq_sum_log_coeff :
    p2WeightedLogQhat T - p2WeightedLogLambda T =
      ∑ b : Bad (nativePlaceSelection T),
        (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : Real) *
          Real.log ‖p2Coefficient T b‖ := by
  have h1 := p2RExact_eq_neg_sum_log_coeff T
  have h2 := p2RExact_eq_weighted_sub T
  linarith

/-- `c0RemainderV2` is `−(2l−1)` times the lambda weighted sum. -/
theorem p2_c0RemainderV2_eq_neg_coeff_mul_weighted :
    c0RemainderV2 T = -((2 * (l.value : Real) - 1) * p2WeightedLogLambda T) := by
  have hsum : (∑ b : Bad (nativePlaceSelection T),
      (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : Real) *
        (-Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖)) =
      -p2WeightedLogLambda T := by
    unfold p2WeightedLogLambda
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  unfold c0RemainderV2
  rw [hsum]
  ring

/-- Weighted-sum form of the exact R1.3 comparison with `c0RemainderV2`. -/
theorem p2RExact_eq_c0_add_weighted_correction :
    p2RExact T = c0RemainderV2 T +
      (((2 * (l.value : Real) - 1) * p2WeightedLogLambda T) +
        (p2WeightedLogLambda T - p2WeightedLogQhat T)) := by
  rw [p2RExact_eq_weighted_sub T, p2_c0RemainderV2_eq_neg_coeff_mul_weighted T]
  ring

end LeanFormal.IUT.XiFPaper.Mzk1P2WeightedSumActual