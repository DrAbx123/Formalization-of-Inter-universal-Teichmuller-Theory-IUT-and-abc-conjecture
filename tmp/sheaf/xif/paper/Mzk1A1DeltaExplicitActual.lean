/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeV2Actual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.PaperRootExtensionFieldScalingActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import Mathlib.Tactic
/-! # A1.6 explicit delta: (1/d)log(mu(J)/mu(O)) = log||lambda|| - delta -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A1DeltaExplicitActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- The actual theta ball lambda*O is the closed ball of radius rootImageRadius. -/
theorem lambdaBall_eq_closedBall :
    rootThetaFieldLambdaO T b =
      Metric.closedBall (0 : rootNormedExtension T b)
        ((rootImageRadius T b : NNReal) : Real) := by
  rw [rootThetaFieldLambdaO_eq_closedBall, ← rootImageRadius_eq_norm_fieldLambda]
/-- Explicit A1.6 delta at b. -/
noncomputable def a1Delta : Real :=
  Real.log (rootImageRadius T b : Real) -
    (1 / (s1915LocalDegree T b : Real)) *
      (Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
        Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal)
/-- The actual lambda ball measure is r^d times the unit-ball measure. -/
theorem lambdaBall_measure_eq :
    rootExtensionHaar T b (rootThetaFieldLambdaO T b) =
      ENNReal.ofReal ((rootImageRadius T b : Real) ^ s1915LocalDegree T b) *
        rootExtensionHaar T b (rootExtensionUnitBall T b) := by
  rw [lambdaBall_eq_closedBall]
  exact s1915_local_measure T b
/-- Delta is nonnegative, with actual q-lattice and theta-ball positivity. -/
theorem a1Delta_nonneg
    (hd : 0 < s1915LocalDegree T b)
    (hQ0 : rootExtensionHaar T b (c0QLattice T b) ≠ 0)
    (hQtop : rootExtensionHaar T b (c0QLattice T b) ≠ ⊤)
    (hO0 : rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hOtop : rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤) :
    0 ≤ a1Delta (T := T) (b := b) := by
  have hsubset : c0QLattice T b ⊆ rootThetaFieldLambdaO T b :=
    c0QLattice_subset_lambda T b
  have hμle : rootExtensionHaar T b (c0QLattice T b) ≤
      rootExtensionHaar T b (rootThetaFieldLambdaO T b) :=
    measure_mono hsubset
  have hballtop : rootExtensionHaar T b (rootThetaFieldLambdaO T b) < ⊤ := by
    rw [lambdaBall_measure_eq T b]
    apply ENNReal.mul_lt_top
    · simp
    · exact rootExtensionUnitBall_measure_lt_top T b
  have hto : (rootExtensionHaar T b (c0QLattice T b)).toReal ≤
      (rootExtensionHaar T b (rootThetaFieldLambdaO T b)).toReal :=
    ENNReal.toReal_mono hballtop.ne hμle
  have hQpos : 0 < (rootExtensionHaar T b (c0QLattice T b)).toReal :=
    ENNReal.toReal_pos hQ0 hQtop
  have hlog : Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal ≤
      Real.log (rootExtensionHaar T b (rootThetaFieldLambdaO T b)).toReal :=
    Real.log_le_log hQpos hto
  have hlamlog : Real.log (rootExtensionHaar T b (rootThetaFieldLambdaO T b)).toReal =
      (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real) +
        Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal := by
    rw [lambdaBall_measure_eq T b]
    rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
    have hrpos : 0 < (rootImageRadius T b : Real) := by
      exact_mod_cast rootImageRadius_pos (T := T) (b := b)
    have hpow : 0 < (rootImageRadius T b : Real) ^ s1915LocalDegree T b :=
      pow_pos hrpos _
    rw [Real.log_mul hpow.ne' (ENNReal.toReal_pos hO0 hOtop).ne']
    rw [Real.log_pow]
  unfold a1Delta
  change 0 ≤ Real.log (rootImageRadius T b : Real) -
    (1 / (s1915LocalDegree T b : Real)) *
      (Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
        Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal)
  have hdpos : (0 : Real) < (s1915LocalDegree T b : Real) := by
    exact_mod_cast hd
  have hmain : Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal ≤
      (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real) +
        Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal :=
    le_trans hlog (le_of_eq hlamlog)
  have hmul := mul_le_mul_of_nonneg_left
    (by linarith : Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
        Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal ≤
      (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real))
    (le_of_lt (one_div_pos.mpr hdpos))
  have hfin : (1 / (s1915LocalDegree T b : Real)) *
      (Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
        Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal) ≤
      Real.log (rootImageRadius T b : Real) := by
    have : (1 / (s1915LocalDegree T b : Real)) *
        ((s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real)) =
        Real.log (rootImageRadius T b : Real) := by
      field_simp [ne_of_gt hdpos]
    calc (1 / (s1915LocalDegree T b : Real)) *
          (Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
            Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal)
        ≤ (1 / (s1915LocalDegree T b : Real)) *
          ((s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real)) := hmul
      _ = Real.log (rootImageRadius T b : Real) := this
  linarith [hfin]

/-- Signed local term: one over d times (log mu(q) - log mu(O)). -/
noncomputable def a1SignedTerm : Real :=
  (1 / (s1915LocalDegree T b : Real)) *
    (Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
      Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal)
/-- Exact A1.6 signed identity: signed term = log r - delta. -/
theorem a1SignedTerm_eq_log_radius_sub_delta :
    a1SignedTerm (T := T) (b := b) =
      Real.log (rootImageRadius T b : Real) - a1Delta (T := T) (b := b) := by
  unfold a1SignedTerm a1Delta
  ring
/-- Equivalent delta identity. -/
theorem a1Delta_eq_log_radius_sub_signedTerm :
    a1Delta (T := T) (b := b) =
      Real.log (rootImageRadius T b : Real) - a1SignedTerm (T := T) (b := b) := by
  rw [a1SignedTerm_eq_log_radius_sub_delta (T := T) (b := b)]
  ring
/-- Signed local inequality with explicit nonneg delta. -/
theorem a1SignedTerm_le_log_radius
    (hd : 0 < s1915LocalDegree T b)
    (hQ0 : rootExtensionHaar T b (c0QLattice T b) ≠ 0)
    (hQtop : rootExtensionHaar T b (c0QLattice T b) ≠ ⊤)
    (hO0 : rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hOtop : rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤) :
    a1SignedTerm (T := T) (b := b) ≤ Real.log (rootImageRadius T b : Real) := by
  have hδ := a1Delta_nonneg (T := T) (b := b) hd hQ0 hQtop hO0 hOtop
  have hid := a1SignedTerm_eq_log_radius_sub_delta (T := T) (b := b)
  linarith

/-- Unnormalized local q log difference log mu(q) - log mu(O). -/
noncomputable def a1LocalQLog : Real :=
  Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
    Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal
/-- Local degree-normalized inequality: q log difference <= d * log r. -/
theorem a1LocalQLog_le_degree_log_radius
    (hd : 0 < s1915LocalDegree T b)
    (hQ0 : rootExtensionHaar T b (c0QLattice T b) ≠ 0)
    (hQtop : rootExtensionHaar T b (c0QLattice T b) ≠ ⊤)
    (hO0 : rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hOtop : rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤) :
    a1LocalQLog (T := T) (b := b) ≤
      (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real) := by
  have hsigned := a1SignedTerm_le_log_radius (T := T) (b := b) hd hQ0 hQtop hO0 hOtop
  have hdR : (0 : Real) < (s1915LocalDegree T b : Real) := by exact_mod_cast hd
  have hmul := mul_le_mul_of_nonneg_left hsigned (le_of_lt hdR)
  unfold a1SignedTerm at hmul
  have hdne : (s1915LocalDegree T b : Real) ≠ 0 := ne_of_gt hdR
  have hleft : (s1915LocalDegree T b : Real) *
      ((1 / (s1915LocalDegree T b : Real)) *
        (Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
          Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal)) =
      a1LocalQLog (T := T) (b := b) := by
    unfold a1LocalQLog
    field_simp [hdne]
  rw [hleft] at hmul
  exact hmul
end LeanFormal.IUT.XiFPaper.Mzk1A1DeltaExplicitActual
end