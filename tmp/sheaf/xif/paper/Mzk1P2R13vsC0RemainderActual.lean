/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2RelativeMassActual
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionFieldScalingActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic

/-! # P2 (R1.3): exact difference between `p2RExact` and `c0RemainderV2` -/

/-
| field | value |
|---|---|
| Status | PROVED: `p2RExact = c0RemainderV2 + p2RExactCorrection`, correction = `Σ_b d_b((2l−1)log‖λ_b‖−log‖c_b‖)`; **no equality assumed** |
| GAP | sign of correction is not determined by current data; only R_exact ≥ 0 is proved independently |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2R13vsC0RemainderActual

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

/-- Exact difference form: `R_exact − c0RemainderV2` is the correction sum. -/
theorem p2RExact_sub_c0RemainderV2_eq_correction :
    p2RExact T - c0RemainderV2 T = p2RExactCorrection T := by
  rw [p2RExact_eq_c0RemainderV2_add_correction T]
  ring

/-- The correction written as `Σ_b d_b(2l·log‖λ_b‖ − log‖qhat_b‖)`. -/
theorem p2RExactCorrection_eq_sum_2l :
    p2RExactCorrection T =
      ∑ b : Bad (nativePlaceSelection T),
        (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : Real) *
          (2 * (l.value : Real) *
              Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ -
            Real.log ‖c0QHat T b‖) := by
  unfold p2RExactCorrection
  apply Finset.sum_congr rfl
  intro b _
  rw [p2_log_norm_qhat_eq_add T b]
  ring

end LeanFormal.IUT.XiFPaper.Mzk1P2R13vsC0RemainderActual