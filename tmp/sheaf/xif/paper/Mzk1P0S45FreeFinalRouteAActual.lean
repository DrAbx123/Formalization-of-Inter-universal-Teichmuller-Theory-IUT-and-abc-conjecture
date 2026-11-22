/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperBadPlaceTensorGeometryActual
import tmp.sheaf.xif.paper.BadPlacePaperNormalizedActual
import tmp.sheaf.xif.paper.BadPlaceNormRatioSourceActual
import tmp.sheaf.xif.paper.BadPlaceNormRatioCorrectionActual
import Mathlib.Tactic

/-! # Route A: S45-free paper-normalized comparison via correction sign

`paperNormalizedCorrection = halfNormRatioCorrectionSum - normRatioCorrectionSum
 = normRatioCorrectionSum * (1/(2l) - 1)`.  Hence a NONNEGATIVE norm-ratio correction
sum (which follows from `1 <= qVFamNormRatio` at every bad place, i.e. the normalized
norm dominating the default norm) forces `paperNormalizedCorrection <= 0`, and then
`paperNormalizedComparison_exact_of_correction_nonpos` gives the comparison WITHOUT the
S45 `qVFamNormRatio = 1` equality.

Explicit remaining gap (NOT assumed as true in the final theorem): deriving
`1 <= qVFamNormRatio` from the donor normalized-vs-default power relation
`||q||_norm = ||q||_def^(1/d)` (with `0 < ||q||_def < 1`, `1 <= d`) still needs the
carrier/instance bridge; here it is kept as an explicit hypothesis on this reduction.
No fake. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P0S45FreeFinalRouteAActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormRatioCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormRatioSourceActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- A nonnegative norm-ratio correction sum, from `1 <= qVFamNormRatio` pointwise. -/
theorem normRatioCorrectionSum_nonneg_of_ratio_ge_one
    (h : ∀ b : Bad (nativePlaceSelection T), 1 ≤ qVFamNormRatio T b) :
    0 ≤ normRatioCorrectionSum T := by
  unfold normRatioCorrectionSum
  exact Finset.sum_nonneg fun b _ =>
    mul_nonneg (badPlaceNativeBadLocalWeight_nonneg T b) (Real.log_nonneg (h b))

/-- If the norm-ratio correction sum is nonnegative, the paper correction is nonpositive:
`correction = sum * (1/(2l) - 1)` and `1/(2l) - 1 <= 0` for `l >= 5`. -/
theorem paperNormalizedCorrection_nonpos_of_sum_nonneg
    (h : 0 ≤ normRatioCorrectionSum T) : paperNormalizedCorrection T ≤ 0 := by
  have htwo : (2 * (l.value : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  have hpos : 0 < 2 * (l.value : ℝ) := by
    have h5 : (0 : ℝ) < l.value := by exact_mod_cast l.prime.pos
    nlinarith
  have hhalf : halfNormRatioCorrectionSum T =
      normRatioCorrectionSum T / (2 * (l.value : ℝ)) := by
    rw [eq_div_iff htwo, mul_comm]
    exact twoL_mul_halfNormRatioCorrectionSum T
  have hfac : paperNormalizedCorrection T =
      normRatioCorrectionSum T * (1 / (2 * (l.value : ℝ)) - 1) := by
    unfold paperNormalizedCorrection
    rw [hhalf]
    ring
  rw [hfac]
  apply mul_nonpos_of_nonneg_of_nonpos h
  have h5 : (5 : ℝ) ≤ l.value := by exact_mod_cast l.ge_five
  have hden : (1 : ℝ) ≤ 2 * (l.value : ℝ) := by nlinarith
  have hinv : 1 / (2 * (l.value : ℝ)) ≤ 1 := by
    rw [div_le_one hpos]
    exact hden
  linarith

/-- **Route A reduction (S45-free conditional form)**: if the norm ratio is at least one
at every bad place, the paper-normalized comparison holds WITHOUT `qVFamNormRatio = 1`. -/
theorem finalPaperNormalizedComparison_noS45_of_ratio_ge_one
    (h : ∀ b : Bad (nativePlaceSelection T), 1 ≤ qVFamNormRatio T b) :
    paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T :=
  paperNormalizedComparison_exact_of_correction_nonpos T
    (paperNormalizedCorrection_nonpos_of_sum_nonneg T
      (normRatioCorrectionSum_nonneg_of_ratio_ge_one T h))

def routeARows : List (String × String × String) :=
  [ ("normRatioCorrectionSum_nonneg_of_ratio_ge_one", "1 <= ratio pointwise => correction sum nonneg", "PROVED"),
    ("paperNormalizedCorrection_nonpos_of_sum_nonneg", "sum nonneg => paper correction <= 0 (1/(2l)-1 <= 0, l>=5)", "PROVED"),
    ("finalPaperNormalizedComparison_noS45_of_ratio_ge_one", "ratio >= 1 => paper comparison WITHOUT S45 equality", "PROVED (reduction)"),
    ("qVFamNormRatio >= 1 from donor power relation", "needs carrier/instance bridge; kept explicit, not assumed in final", "EXPLICIT REMAINING GAP") ]

theorem routeARows_length : routeARows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P0S45FreeFinalRouteAActual

end