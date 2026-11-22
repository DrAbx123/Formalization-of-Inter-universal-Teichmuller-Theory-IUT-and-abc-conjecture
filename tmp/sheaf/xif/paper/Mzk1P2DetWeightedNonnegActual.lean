import tmp.sheaf.xif.paper.Mzk1P2DetCoefficientActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionFieldScalingActual
import Mathlib.Tactic

/-! # P2: weighted determinant log is nonpositive and R1.3 mass difference

No dependency on the red relative-mass file: the qhat/lambda factorization and
nonzero lemmas are re-proved from the green label-block coefficient file.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1S1915DegreeFinrankActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Weighted sum of local coefficient log-norms. -/
noncomputable def weightedDetLog
    (w : Bad (nativePlaceSelection T) -> Real)
    (c : RootExtensionProductCarrier T) : Real :=
  ∑ b : Bad (nativePlaceSelection T), w b * Real.log ‖c b‖

theorem weightedDetLog_nonpos
    (w : Bad (nativePlaceSelection T) -> Real)
    (c : RootExtensionProductCarrier T)
    (hw : ∀ b, 0 ≤ w b)
    (hpos : ∀ b, 0 < ‖c b‖)
    (hc : ∀ b, ‖c b‖ ≤ 1) :
    weightedDetLog T w c ≤ 0 := by
  unfold weightedDetLog
  apply Finset.sum_nonpos
  intro b _
  apply mul_nonpos_of_nonneg_of_nonpos (hw b)
  exact Real.log_nonpos (le_of_lt (hpos b)) (hc b)

/-- Log of qhat = log lambda + log coefficient. -/
theorem p2_log_norm_qhat_eq_add (b : Bad (nativePlaceSelection T)) :
    Real.log ‖c0QHat T b‖ =
      Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ +
        Real.log ‖p2Coefficient T b‖ := by
  rw [p2QHat_eq_lambda_mul_coefficient T b, norm_mul]
  exact Real.log_mul
    (norm_ne_zero_iff.mpr (p2_lambda_ne_zero T b))
    (norm_ne_zero_iff.mpr (p2Coeff_ne_zero T b))

/-- Pointwise R1.3 factor: log lambda - log qhat = - log coefficient. -/
theorem p2_log_lambda_sub_log_qhat (b : Bad (nativePlaceSelection T)) :
    Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ -
        Real.log ‖c0QHat T b‖ =
      - Real.log ‖p2Coefficient T b‖ := by
  rw [p2_log_norm_qhat_eq_add T b]
  ring

/-- R1.3 weighted relative mass difference with arbitrary local weights. -/
noncomputable def p2R13MassDifference
    (w : Bad (nativePlaceSelection T) -> Real) : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    w b *
      (Real.log ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ -
        Real.log ‖c0QHat T b‖)

/-- R1.3 mass difference is the negative weighted coefficient log sum. -/
theorem p2R13MassDifference_eq_neg_weightedDetLog
    (w : Bad (nativePlaceSelection T) -> Real) :
    p2R13MassDifference T w = - weightedDetLog T w (p2PureTensorCoefficient T) := by
  unfold p2R13MassDifference weightedDetLog p2PureTensorCoefficient
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [p2_log_lambda_sub_log_qhat T b]
  ring

/-- The actual s1915-degree weighted determinant log. -/
noncomputable def p2WeightedDetLog : Real :=
  weightedDetLog T
    (fun b => (s1915LocalDegree T b : Real))
    (p2PureTensorCoefficient T)

theorem p2WeightedDetLog_nonpos : p2WeightedDetLog T ≤ 0 := by
  apply weightedDetLog_nonpos T
    (fun b => (s1915LocalDegree T b : Real))
    (p2PureTensorCoefficient T)
  · exact fun b => Nat.cast_nonneg _
  · exact fun b => norm_pos_iff.mpr (p2Coeff_ne_zero T b)
  · exact fun b => p2Coefficient_norm_le_one T b

/-- Actual R1.3 mass difference with s1915 degrees. -/
noncomputable def p2R13Exact : Real :=
  p2R13MassDifference T (fun b => (s1915LocalDegree T b : Real))

theorem p2R13Exact_eq_neg_p2WeightedDetLog :
    p2R13Exact T = - p2WeightedDetLog T :=
  p2R13MassDifference_eq_neg_weightedDetLog T
    (fun b => (s1915LocalDegree T b : Real))

theorem p2R13Exact_nonneg : 0 ≤ p2R13Exact T := by
  rw [p2R13Exact_eq_neg_p2WeightedDetLog T]
  exact neg_nonneg.mpr (p2WeightedDetLog_nonpos T)

#check weightedDetLog
#check weightedDetLog_nonpos
#check p2R13MassDifference
#check p2R13MassDifference_eq_neg_weightedDetLog
#check p2WeightedDetLog
#check p2WeightedDetLog_nonpos
#check p2R13Exact
#check p2R13Exact_eq_neg_p2WeightedDetLog
#check p2R13Exact_nonneg
end LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
end
