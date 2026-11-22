/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2LabelBlockCoefficientActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionFieldScalingActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import Mathlib.Tactic

/-! # P2: actual theta values -> allowed λO image -/

/-
| field | value |
|---|---|
| Status | PROVED: every actual theta value at a `ThetaLabel` lies in the allowed λO region; λ itself lies in λO |
| GAP | allowed re-root / unit operations from the source production are not constructed; only static theta image inclusion is proved |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2ThetaAllowedImageActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
open scoped BigOperators ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Every actual theta value at a `ThetaLabel` lies in the allowed λO region. -/
theorem p2ThetaValue_mem_allowedO
    (b : Bad (nativePlaceSelection T)) (j : ThetaLabel (l := l)) :
    rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) ∈
      rootThetaFieldLambdaO T b := by
  have htheta : ‖rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j)‖ ≤
      (rootImageRadius T b : Real) :=
    rootImageRadius_ge T b j
  have hlam : (rootImageRadius T b : Real) = ‖rootThetaFieldLambda T b‖ :=
    rootImageRadius_eq_norm_fieldLambda T b
  have hle : ‖rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j)‖ ≤
      ‖rootThetaFieldLambda T b‖ := by
    rw [← hlam]
    exact htheta
  have hpos : 0 < ‖rootThetaFieldLambda T b‖ := by
    rw [← hlam]
    exact_mod_cast rootImageRadius_pos (T := T) (b := b)
  have hne : rootThetaFieldLambda T b ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hpos)
  unfold rootThetaFieldLambdaO
  refine ⟨rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) /
    rootThetaFieldLambda T b, ?_, ?_⟩
  · unfold rootExtensionUnitBall
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [sub_zero]
    rw [norm_div]
    exact (div_le_one hpos).mpr hle
  · change rootThetaFieldLambda T b *
      (rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) /
        rootThetaFieldLambda T b) =
        rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j)
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ _ hne

/-- `λ` itself lies in λO. -/
theorem p2Lambda_mem_allowedO (b : Bad (nativePlaceSelection T)) :
    rootThetaFieldLambda T b ∈ rootThetaFieldLambdaO T b := by
  refine ⟨1, ?_, ?_⟩
  · unfold rootExtensionUnitBall
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp
  · change rootThetaFieldLambda T b * 1 = rootThetaFieldLambda T b
    rw [mul_one]

/-- The `ThetaLabel` theta image set lies in λO. -/
theorem p2ThetaImageSet_subset_allowedO (b : Bad (nativePlaceSelection T)) :
    Set.range (fun j : ThetaLabel (l := l) =>
      rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j)) ⊆
      rootThetaFieldLambdaO T b := by
  rintro x ⟨j, rfl⟩
  exact p2ThetaValue_mem_allowedO T b j

end LeanFormal.IUT.XiFPaper.Mzk1P2ThetaAllowedImageActual