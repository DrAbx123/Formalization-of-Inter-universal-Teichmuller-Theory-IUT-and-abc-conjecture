/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GeneralNormalizedNormBySpectralUniqueness
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import tmp.sheaf.xif.paper.Mzk1P0S45FreeFinalRouteAActual
import tmp.sheaf.xif.paper.BadPlacePaperNormalizedComparisonActual
import tmp.sheaf.xif.paper.BadPlaceNormRatioCorrectionActual
import tmp.sheaf.xif.paper.BadPlacePaperNormalizedActual
import Mathlib.Tactic

/-! # Unconditional qVFam normalized-vs-default norm bridge (S45-free)

Donor: `‖x‖_L = absNorm^(-(nu x)/d)`.  Default: `‖toC x‖_C = absNorm^m` with
`m = toAdd (unzero (v (toC x))) = -nu x`.  Hence
`qVFamNormalizedNorm = (qVFamDefaultNorm)^(1/d)`; since `0 < default < 1` and `1 ≤ d`,
`1 ≤ qVFamNormRatio`.  This is a POWER relation; no norm equality and no S45 equality. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P0QVFamNormBridgeDonorActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.GeneralNormalizedNormBySpectralUniqueness
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.BadPlaceNormRatioCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedActual
open LeanFormal.IUT.XiFPaper.Mzk1P0S45FreeFinalRouteAActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Default norm is positive. -/
theorem qVFamDefaultNorm_pos : 0 < qVFamDefaultNorm T b := by
  unfold qVFamDefaultNorm
  exact norm_pos_iff.mpr (qVFamily T b).q_ne_zero

/-- Default norm is less than one (actual q parameter). -/
theorem qVFamDefaultNorm_lt_one : qVFamDefaultNorm T b < 1 := by
  unfold qVFamDefaultNorm
  exact qNorm_lt_one (qVFamily T b)

/-- **Unconditional norm bridge**: normalized norm is the `1/d`-power of the default
norm at the same qVFamily element. -/
theorem qVFamNormalizedNorm_eq_defaultNorm_rpow :
    qVFamNormalizedNorm T b =
      (qVFamDefaultNorm T b) ^
        (1 / (relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) : ℝ)) := by
  have hx : qVFamNormalizedGenerator T b ≠ 0 := qVFamNormalizedGenerator_ne_zero T b
  have hnorm := generalNormalizedNormFormula (F := T.arithmetic.F)
    (qVFamTensorPlace T b) (qVFamNormalizedGenerator T b) hx
  have hx' : toC (qVFamTensorPlace T b) (qVFamNormalizedGenerator T b) ≠ 0 := by
    rw [toC_apply]; exact hx
  let xC := toC (qVFamTensorPlace T b) (qVFamNormalizedGenerator T b)
  let val := Valued.v xC
  have hval : val ≠ 0 :=
    valuation_ne_zero_of_ne_zero (qVFamTensorPlace T b) xC hx'
  let m : ℤ := Multiplicative.toAdd (α := ℤ) (WithZero.unzero (x := val) hval)
  have hdef := norm_eq_absNorm_zpow (F := T.arithmetic.F) (P := qVFamTensorPlace T b) xC hx'
  have h2 : Multiplicative.toAdd
      (WithZero.unzero (x := val)
        (valuation_ne_zero_of_ne_zero (qVFamTensorPlace T b) xC hx')) = m := by
    have h1 : WithZero.unzero (x := val)
        (valuation_ne_zero_of_ne_zero (qVFamTensorPlace T b) xC hx') =
        WithZero.unzero (x := val) hval := by
      apply WithZero.coe_injective
      simp [WithZero.coe_unzero]
    rw [h1]
  have hlog : WithZero.log val = m := by
    rw [show val = (↑(WithZero.unzero (x := val) hval) : WithZero (Multiplicative ℤ)) from (WithZero.coe_unzero hval).symm]
    rfl
  have hnu : nu (qVFamTensorPlace T b) (qVFamNormalizedGenerator T b) = -m := by
    unfold nu
    rw [hlog]
  have hm : ((m : ℤ) : ℝ) =
      -(nu (qVFamTensorPlace T b) (qVFamNormalizedGenerator T b) : ℝ) := by
    rw [hnu]
    push_cast
    ring
  have hdef' : qVFamDefaultNorm T b =
      (absNorm (qVFamTensorPlace T b)) ^ ((m : ℤ) : ℝ) := by
    change ‖(qVFamily T b).q‖ = (absNorm (qVFamTensorPlace T b)) ^ ((m : ℤ) : ℝ)
    have hstep :
        (↑(Ideal.absNorm (qVFamTensorPlace T b).maximalIdeal.asIdeal) ^
          Multiplicative.toAdd
            (WithZero.unzero (x := val)
              (valuation_ne_zero_of_ne_zero (qVFamTensorPlace T b) xC hx')) : ℝ) =
        (↑(Ideal.absNorm (qVFamTensorPlace T b).maximalIdeal.asIdeal) ^
          ((m : ℤ) : ℝ)) := by
      have hc := congrArg (fun z : ℤ =>
        (↑(Ideal.absNorm (qVFamTensorPlace T b).maximalIdeal.asIdeal) : ℝ) ^ (z : ℝ)) h2
      simpa [Real.rpow_intCast] using hc
    exact hdef.trans hstep
  have hnorm' : qVFamNormalizedNorm T b =
      (absNorm (qVFamTensorPlace T b)) ^
        (-(nu (qVFamTensorPlace T b) (qVFamNormalizedGenerator T b) : ℝ) /
          (d (qVFamTensorPlace T b) : ℝ)) := by
    change ‖qVFamNormalizedGenerator T b‖ =
      (absNorm (qVFamTensorPlace T b)) ^
        (-(nu (qVFamTensorPlace T b) (qVFamNormalizedGenerator T b) : ℝ) /
          (d (qVFamTensorPlace T b) : ℝ))
    exact hnorm
  calc qVFamNormalizedNorm T b
      = (absNorm (qVFamTensorPlace T b)) ^
          (-(nu (qVFamTensorPlace T b) (qVFamNormalizedGenerator T b) : ℝ) /
            (d (qVFamTensorPlace T b) : ℝ)) := hnorm'
    _ = (absNorm (qVFamTensorPlace T b)) ^
          (((m : ℤ) : ℝ) *
            (1 / (relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) : ℝ))) := by
        rw [hm]
        congr 1
        ring
    _ = ((absNorm (qVFamTensorPlace T b)) ^
          ((m : ℤ) : ℝ)) ^
          (1 / (relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) : ℝ)) := by
        rw [Real.rpow_mul (absNorm_pos (qVFamTensorPlace T b)).le]
    _ = (qVFamDefaultNorm T b) ^
          (1 / (relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) : ℝ)) := by
        rw [hdef']

/-- **Unconditional ratio bound**: the normalized norm dominates the default norm,
hence `1 ≤ qVFamNormRatio`. -/
theorem qVFamNormRatio_ge_one : 1 ≤ qVFamNormRatio T b := by
  have hdpos : 0 < relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) :=
    relativeCompletionDegree_pos (k := ℚ) (qVFamTensorPlace T b)
  have hd : 1 ≤ relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) :=
    Nat.succ_le_of_lt hdpos
  have hdefpos : 0 < qVFamDefaultNorm T b := qVFamDefaultNorm_pos T b
  have hdeflt : qVFamDefaultNorm T b < 1 := qVFamDefaultNorm_lt_one T b
  have hdR : (0 : ℝ) < (relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) : ℝ) := by
    exact_mod_cast hdpos
  have hexp : (1 : ℝ) / (relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) : ℝ) ≤ 1 := by
    rw [div_le_one hdR]
    exact_mod_cast hd
  have hge : qVFamDefaultNorm T b ≤
      (qVFamDefaultNorm T b) ^
        (1 / (relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) : ℝ)) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hdefpos (le_of_lt hdeflt) hexp
  have hnorm_ge : qVFamDefaultNorm T b ≤ qVFamNormalizedNorm T b := by
    rw [qVFamNormalizedNorm_eq_defaultNorm_rpow T b]
    exact hge
  unfold qVFamNormRatio
  exact (one_le_div hdefpos).mpr hnorm_ge

/-- **Final S45-free paper comparison** (unconditional): correction is nonpositive, so
the paper-normalized comparison holds without `qVFamNormRatio = 1`. -/
theorem finalPaperNormalizedComparison_noS45
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] :
    paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T := by
  have h : ∀ b : Bad (nativePlaceSelection T), 1 ≤ qVFamNormRatio T b :=
    fun b => qVFamNormRatio_ge_one T b
  exact finalPaperNormalizedComparison_noS45_of_ratio_ge_one T h

def normBridgeRows : List (String × String × String) :=
  [ ("qVFamNormalizedNorm_eq_defaultNorm_rpow", "normalized = default^(1/d) (donor power relation, same element)", "PROVED"),
    ("qVFamNormRatio_ge_one", "1 <= qVFamNormRatio (0<default<1, 1<=d)", "PROVED"),
    ("finalPaperNormalizedComparison_noS45", "paper comparison WITHOUT S45 norm equality", "PROVED (unconditional)"),
    ("S45 / qVFamNormRatio = 1", "correction-zero/strict source condition", "EXPLICIT CONDITION (not needed for inequality)") ]

theorem normBridgeRows_length : normBridgeRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P0QVFamNormBridgeDonorActual

end