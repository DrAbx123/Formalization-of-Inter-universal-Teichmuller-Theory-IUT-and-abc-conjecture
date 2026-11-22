import tmp.sheaf.xif.paper.Mzk1P2LabelBlockCoefficientActual
import tmp.sheaf.xif.paper.Mzk1S1915DegreeFinrankActual
import tmp.sheaf.xif.paper.O2QrootGlueActual
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.PaperRootExtensionFieldScalingActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import Mathlib.Tactic

/-! # P2: pure-tensor determinant coefficient norms

The product carrier is the actual finite product of root extensions.  The
determinant normalization of a pure tensor coefficient family is the product of
the local norms (the tensor determinant); this is NOT the Pi sup norm.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P2DetCoefficientActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
open LeanFormal.IUT.XiFPaper.O2QrootGlueActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Tensor determinant norm of a pure coefficient family: product of local norms. -/
noncomputable def detCoefficientNorm
    (c : RootExtensionProductCarrier T) : Real :=
  ∏ b : Bad (nativePlaceSelection T), ‖c b‖

theorem detCoefficientNorm_eq_prod (c : RootExtensionProductCarrier T) :
    detCoefficientNorm T c =
      ∏ b : Bad (nativePlaceSelection T), ‖c b‖ := rfl

theorem detCoefficientNorm_nonneg (c : RootExtensionProductCarrier T) :
    0 ≤ detCoefficientNorm T c := by
  unfold detCoefficientNorm
  exact Finset.prod_nonneg (fun b _ => norm_nonneg _)

/-- Product of local norms ≤ 1 when every local coefficient has norm ≤ 1. -/
theorem norm_prod_le_one
    (c : RootExtensionProductCarrier T)
    (hc : ∀ b : Bad (nativePlaceSelection T), ‖c b‖ ≤ 1) :
    detCoefficientNorm T c ≤ 1 := by
  unfold detCoefficientNorm
  exact Finset.prod_le_one (fun b _ => norm_nonneg _) (fun b _ => hc b)

/-- Log of the tensor determinant norm is the sum of local logs. -/
theorem log_norm_prod_eq_sum
    (c : RootExtensionProductCarrier T)
    (hpos : ∀ b : Bad (nativePlaceSelection T), 0 < ‖c b‖) :
    Real.log (detCoefficientNorm T c) =
      ∑ b : Bad (nativePlaceSelection T), Real.log ‖c b‖ := by
  unfold detCoefficientNorm
  rw [Real.log_prod (fun b _ => (hpos b).ne')]

/-- lambda_b is nonzero. -/
theorem p2_lambda_ne_zero (b : Bad (nativePlaceSelection T)) :
    rootThetaFieldLambda T b ≠ 0 := by
  have hpos : 0 < ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ := by
    rw [← rootImageRadius_eq_norm_fieldLambda]
    exact_mod_cast rootImageRadius_pos (T := T) (b := b)
  exact norm_ne_zero_iff.mp (ne_of_gt hpos)

/-- qhat_b is nonzero. -/
theorem p2_qhat_ne_zero (b : Bad (nativePlaceSelection T)) :
    c0QHat T b ≠ 0 := by
  unfold c0QHat c0Alpha
  exact pow_ne_zero _ (qrootElem_ne_zero T b)

/-- The R1.2 coefficient is nonzero. -/
theorem p2Coeff_ne_zero (b : Bad (nativePlaceSelection T)) :
    p2Coefficient T b ≠ 0 :=
  div_ne_zero (p2_qhat_ne_zero T b) (p2_lambda_ne_zero T b)

/-- Actual pure-tensor coefficient determinant norm ≤ 1. -/
theorem p2DetCoefficientNorm_le_one :
    detCoefficientNorm T (p2PureTensorCoefficient T) ≤ 1 :=
  norm_prod_le_one T (p2PureTensorCoefficient T)
    (fun b => p2Coefficient_norm_le_one T b)

theorem p2DetCoefficientNorm_pos :
    0 < detCoefficientNorm T (p2PureTensorCoefficient T) := by
  unfold detCoefficientNorm p2PureTensorCoefficient
  exact Finset.prod_pos (fun b _ => norm_pos_iff.mpr (p2Coeff_ne_zero T b))

/-- Actual log determinant decomposition. -/
theorem p2_log_detCoefficientNorm_eq_sum :
    Real.log (detCoefficientNorm T (p2PureTensorCoefficient T)) =
      ∑ b : Bad (nativePlaceSelection T),
        Real.log ‖p2Coefficient T b‖ :=
  log_norm_prod_eq_sum T (p2PureTensorCoefficient T)
    (fun b => norm_pos_iff.mpr (p2Coeff_ne_zero T b))

#check detCoefficientNorm
#check norm_prod_le_one
#check log_norm_prod_eq_sum
#check p2DetCoefficientNorm_le_one
#check p2_log_detCoefficientNorm_eq_sum
end LeanFormal.IUT.XiFPaper.Mzk1P2DetCoefficientActual
end
