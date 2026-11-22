import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.PaperRootExtensionFieldScalingActual
import tmp.sheaf.xif.paper.Mzk1KummerNormBoundBridgeActual
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import Mathlib.Tactic

/-!
# Route C0 v2: corrected theta source H_root = lambda_b * O_b

V1 used alpha_b = qroot (label-1 theta).  V2 uses the actual coordinatewise
maximum theta value lambda_b = rootThetaFieldLambda T b, so the product H_root
is exactly the original theta image hull
(`rootExtensionProductFieldScaledHull = rootExtensionProductImageHull`).

qhat_b O_b subset lambda_b O_b because ||qhat_b|| <= rootImageRadius_b
= ||lambda_b||.  Remainder uses r_b = ||lambda_b||; arch/infinite terms are
listed as a separate gap.  No comparison input.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.O2QrootGlueActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerNormBoundBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory
open scoped BigOperators ENNReal

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem c0QHat_norm_le_radius (b : Bad (nativePlaceSelection T)) :
    ‖c0QHat T b‖ ≤ (rootImageRadius T b : Real) := by
  have h := thetaOne_pow_norm_le_radius (T := T) (b := b)
  simpa [c0QHat, c0Alpha, qrootElem, qrootUnit, rootNormedUnit,
    LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual.thetaPilotImage_one_apply] using h

theorem c0QLattice_subset_lambda (b : Bad (nativePlaceSelection T)) :
    c0QLattice T b ⊆ rootThetaFieldLambdaO T b := by
  rintro z ⟨y, hy, rfl⟩
  have hqhat_le : ‖c0QHat T b‖ ≤ ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ := by
    rw [← rootImageRadius_eq_norm_fieldLambda]
    exact c0QHat_norm_le_radius T b
  have hlam_norm_pos : 0 < ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ := by
    rw [← rootImageRadius_eq_norm_fieldLambda]
    exact_mod_cast rootImageRadius_pos (T := T) (b := b)
  have hlam_ne : rootThetaFieldLambda T b ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hlam_norm_pos)
  refine ⟨(c0QHat T b / rootThetaFieldLambda T b) * y, ?_, ?_⟩
  · change y ∈ rootExtensionUnitBall T b at hy
    change (c0QHat T b / rootThetaFieldLambda T b) * y ∈ rootExtensionUnitBall T b
    unfold rootExtensionUnitBall at hy ⊢
    rw [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
    simp only [sub_zero] at hy ⊢
    rw [norm_mul]
    have hratio : ‖c0QHat T b / rootThetaFieldLambda T b‖ ≤ 1 := by
      rw [norm_div]
      exact (div_le_one hlam_norm_pos).mpr hqhat_le
    exact mul_le_one₀ hratio (norm_nonneg _) hy
  · change rootThetaFieldLambda T b •
      (c0QHat T b / rootThetaFieldLambda T b * y) = c0QHat T b * y
    rw [smul_eq_mul, ← mul_assoc]
    field_simp [hlam_ne]

theorem c0ProductQ_subset_imageHull :
    c0ProductQ T ⊆ rootExtensionProductImageHull T := by
  rw [← rootExtensionProductFieldScaledHull_eq_imageHull]
  intro x hx b hb
  exact c0QLattice_subset_lambda T b (hx b hb)

theorem c0ProductHaar_le_imageHull :
    rootExtensionProductHaar T (c0ProductQ T) ≤
      rootExtensionProductHaar T (rootExtensionProductImageHull T) :=
  measure_mono (c0ProductQ_subset_imageHull T)

noncomputable def c0RemainderV2 : Real :=
  ((2 * (l.value : Real) - 1) *
    ∑ b : Bad (nativePlaceSelection T),
      (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : Real) *
        (-Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖))

theorem c0RemainderV2_nonneg : 0 ≤ c0RemainderV2 T := by
  unfold c0RemainderV2
  have hcoef : 0 ≤ 2 * (l.value : Real) - 1 := by
    have : (5 : Real) ≤ l.value := by exact_mod_cast l.ge_five
    linarith
  have hterm : ∀ b : Bad (nativePlaceSelection T),
      0 ≤ (Module.finrank ℚ_[(LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorP T b)] (rootNormedExtension T b) : Real) *
        (-Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖) := by
    intro b
    apply mul_nonneg
    · exact_mod_cast Nat.zero_le _
    · have hnormpos : 0 < ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ := by
        rw [← rootImageRadius_eq_norm_fieldLambda]
        exact_mod_cast rootImageRadius_pos (T := T) (b := b)
      have hnormle : ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ ≤ 1 := by
        rw [← rootImageRadius_eq_norm_fieldLambda]
        exact s1915_rootImageRadius_le_one T b
      have hlog : Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ ≤ 0 :=
        Real.log_nonpos (le_of_lt hnormpos) hnormle
      linarith
  exact mul_nonneg hcoef (Finset.sum_nonneg (fun b _ => hterm b))

theorem routeC0V2_constructed :
    (∀ b, c0QLattice T b ⊆ rootThetaFieldLambdaO T b) ∧
      c0ProductQ T ⊆ rootExtensionProductImageHull T ∧
      rootExtensionProductHaar T (c0ProductQ T) ≤
        rootExtensionProductHaar T (rootExtensionProductImageHull T) ∧
      0 ≤ c0RemainderV2 T := by
  exact ⟨c0QLattice_subset_lambda T, c0ProductQ_subset_imageHull T,
    c0ProductHaar_le_imageHull T, c0RemainderV2_nonneg T⟩

#print axioms routeC0V2_constructed

end LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
