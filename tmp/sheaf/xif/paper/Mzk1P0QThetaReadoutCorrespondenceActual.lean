/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.three_gap_closure_20261114.QhatHaarScalingReuse
import tmp.sheaf.xif.paper.Mzk1A1DeltaExplicitActual
import tmp.sheaf.xif.paper.Mzk1HullUBLocalThirdActual
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeV2Actual
import tmp.sheaf.xif.paper.Mzk1P0RouteC0GlobalReadoutActual
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction
import tmp.sheaf.xif.paper.Mzk1P3ProductHaarPiActual
import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import Mathlib.Tactic
/-! # q/Theta readout correspondence under the explicit qhat Haar scaling

This file does not assume paperNetSlack or R37.  It isolates the single explicit
factor gap: the local qhat Haar scaling
  mu(c0QLattice_b) = ofReal(||qhat_b||^{d_b}) * mu(O_b).
Under that scaling, qhatLogReadout equals log||qhat_b|| and the global q product
normalized log is the degree-weighted sum of the native q readouts.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0QThetaReadoutCorrespondenceActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P3ProductHaarPiActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.ThreeGapClosure20261114
open LeanFormal.IUT.XiFPaper.Mzk1A1DeltaExplicitActual
open LeanFormal.IUT.XiFPaper.Mzk1HullUBLocalThirdActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1P0RouteC0GlobalReadoutActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open MeasureTheory
open scoped BigOperators
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- Local signed qhat log readout, defined here to avoid depending on any
pending readout file. -/
noncomputable def qhatLogReadout : Real :=
  (1 / (s1915LocalDegree T b : Real)) *
    (Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
      Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal)
/-- The single explicit factor gap: local qhat Haar scaling law. -/
def qhatHaarScaling : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    rootExtensionHaar T b (c0QLattice T b) =
      ENNReal.ofReal (‖c0QHat T b‖ ^ s1915LocalDegree T b) *
        rootExtensionHaar T b (rootExtensionUnitBall T b)
theorem c0QHat_ne_zero : c0QHat T b ≠ 0 := by
  unfold c0QHat
  exact pow_ne_zero _ (c0Alpha_ne_zero T b)
/-- Native q readout is the log of the q norm (q norm < 1). -/
theorem nativeQReadout_eq_log_norm :
    nativeQReadout T b = Real.log ‖(qVFamily T b).q‖ := by
  unfold nativeQReadout
  rw [abs_of_neg (Real.log_neg (qNorm_pos (qVFamily T b)) (qNorm_lt_one (qVFamily T b)))]
  ring
/-- Under the explicit scaling, qhatLogReadout is exactly log||qhat||. -/
theorem qhatLogReadout_eq_log_norm_of_scaling
    (hd : 0 < s1915LocalDegree T b)
    (hscale : qhatHaarScaling T)
    (hO0 : rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hOtop : rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤) :
    qhatLogReadout T b = Real.log ‖c0QHat T b‖ := by
  have hqne : c0QHat T b ≠ 0 := c0QHat_ne_zero T b
  have hqpos : 0 < ‖c0QHat T b‖ := norm_pos_iff.mpr hqne
  have hfac := hscale b
  have hOpos : 0 < (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal :=
    ENNReal.toReal_pos hO0 hOtop
  have hOtopNE : rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤ := hOtop
  have hqne : c0QHat T b ≠ 0 := c0QHat_ne_zero T b
  have hqpos : 0 < ‖c0QHat T b‖ := norm_pos_iff.mpr hqne
  have hpow : 0 < ‖c0QHat T b‖ ^ s1915LocalDegree T b :=
    pow_pos hqpos _
  have hlog : Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal =
      (s1915LocalDegree T b : Real) * Real.log ‖c0QHat T b‖ +
        Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal := by
    rw [hfac]
    rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
    change Real.log (‖c0QHat T b‖ ^ s1915LocalDegree T b *
      (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal) =
      (s1915LocalDegree T b : Real) * Real.log ‖c0QHat T b‖ +
        Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal
    rw [Real.log_mul hpow.ne' hOpos.ne']
    rw [Real.log_pow]
  unfold qhatLogReadout
  have hdpos : (0 : Real) < (s1915LocalDegree T b : Real) := by
    exact_mod_cast hd
  rw [hlog]
  field_simp [ne_of_gt hdpos]
  ring
/-- Global q product normalized log is the degree-weighted sum of log||qhat_b||. -/
theorem c0ProductQ_normalizedLog_eq_sum_qhat (hd : ∀ b, 0 < s1915LocalDegree T b)
    (hscale : qhatHaarScaling T)
    (hQ0 : ∀ b, rootExtensionHaar T b (c0QLattice T b) ≠ 0)
    (hQtop : ∀ b, rootExtensionHaar T b (c0QLattice T b) ≠ ⊤)
    (hO0 : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hOtop : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤) :
    rootExtensionProductNormalizedLog T (c0ProductQ T) =
      ∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) * Real.log ‖c0QHat T b‖ := by
  have hpi := productNormalizedLog_pi T (fun b => c0QLattice T b) hQ0 hQtop hO0 hOtop
  unfold c0ProductQ at hpi ⊢
  rw [hpi]
  apply Finset.sum_congr rfl
  intro b _
  have h := hscale b
  have hOpos : 0 < (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal :=
    ENNReal.toReal_pos (hO0 b) (hOtop b)
  have hlog : Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal =
      (s1915LocalDegree T b : Real) * Real.log ‖c0QHat T b‖ +
        Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal := by
    have hqne : c0QHat T b ≠ 0 := c0QHat_ne_zero T b
    have hqpos : 0 < ‖c0QHat T b‖ := norm_pos_iff.mpr hqne
    have hpow : 0 < ‖c0QHat T b‖ ^ s1915LocalDegree T b :=
      pow_pos hqpos _
    rw [h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    change Real.log (‖c0QHat T b‖ ^ s1915LocalDegree T b *
      (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal) =
      (s1915LocalDegree T b : Real) * Real.log ‖c0QHat T b‖ +
        Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal
    rw [Real.log_mul hpow.ne' hOpos.ne']
    rw [Real.log_pow]
  rw [hlog]
  ring

/-- Unconditional qhatHaarScaling from S865 and distribHaarChar. -/
theorem qhatHaarScaling_actual : qhatHaarScaling T := fun b =>
  qhat_haar_scaling_actual (T := T) (b := b)
/-- qhatLogReadout is exactly log||qhat|| (actual scaling, no conditions). -/
theorem qhatLogReadout_eq_log_norm :
    qhatLogReadout T b = Real.log ‖c0QHat T b‖ :=
  qhat_signed_readout_eq_log_norm (T := T) (b := b)
/-- qhat norm is < 1, so the signed readout equals -|log||qhat|||. -/
theorem qhatLogReadout_eq_neg_abs_log_norm :
    qhatLogReadout T b = -|Real.log ‖c0QHat T b‖| := by
  rw [qhatLogReadout_eq_log_norm]
  have hqpos : 0 < ‖c0QHat T b‖ := norm_pos_iff.mpr (pow_ne_zero _ (c0Alpha_ne_zero T b))
  have hqlt : ‖c0QHat T b‖ < 1 :=
    lt_of_le_of_lt (c0QHat_norm_le_radius T b)
      (rootImageRadius_lt_one (T := T) (b := b))
  rw [abs_of_neg (Real.log_neg hqpos hqlt)]
  ring
/-- Unconditional global correspondence: no hd/hscale/hQ/hO hypotheses. -/
theorem c0ProductQ_normalizedLog_eq_sum_qhat_actual :
    rootExtensionProductNormalizedLog T (c0ProductQ T) =
      ∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) * Real.log ‖c0QHat T b‖ :=
  c0ProductQ_normalizedLog_eq_sum_qhat T
    (fun b => local_degree_pos (T := T) (b := b)) (qhatHaarScaling_actual T)
    (fun b => (qhat_lattice_measure_pos (T := T) b).ne')
    (fun b => ne_of_lt (qhat_lattice_measure_lt_top (T := T) b))
    (fun b => (rootExtensionUnitBall_measure_pos T b).ne')
    (fun b => (rootExtensionUnitBall_measure_lt_top T b).ne)
/-- Signed paper form: degree-weighted qhat signed logs are <= s1915ClosedForm-1. -/
theorem sum_degree_qhatLogReadout_le_closedForm_sub_one :
    (∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) * qhatLogReadout T b) ≤
      s1915ClosedForm T - 1 := by
  have hleft : (∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) * qhatLogReadout T b) =
      rootExtensionProductNormalizedLog T (c0ProductQ T) := by
    have hsum := c0ProductQ_normalizedLog_eq_sum_qhat_actual (T := T)
    rw [hsum]
    apply Finset.sum_congr rfl
    intro b _
    rw [qhatLogReadout_eq_log_norm]
  haveI : Nonempty (Bad (nativePlaceSelection T)) := by
    obtain ⟨p, hp⟩ := nativePlaceSelection_nonempty (T := T)
    exact ⟨⟨p, hp⟩⟩
  rw [hleft]
  have hQ0prod : rootExtensionProductHaar T (c0ProductQ T) ≠ 0 := by
    unfold c0ProductQ
    rw [productHaar_pi]
    exact Finset.prod_ne_zero_iff.mpr
      (fun b _ => ne_of_gt (qhat_lattice_measure_pos (T := T) b))
  have hQtopprod : rootExtensionProductHaar T (c0ProductQ T) ≠ ⊤ := by
    unfold c0ProductQ
    rw [productHaar_pi]
    exact ne_of_lt (ENNReal.prod_lt_top
      (fun b _ => qhat_lattice_measure_lt_top (T := T) b))
  have hH0 : rootExtensionProductHaar T (rootExtensionProductImageHull T) ≠ 0 :=
    ne_of_gt (rootExtensionProductImageHull_measure_pos_lt_top T).1
  have hHtop : rootExtensionProductHaar T (rootExtensionProductImageHull T) ≠ ⊤ :=
    ne_of_lt (rootExtensionProductImageHull_measure_pos_lt_top T).2
  exact c0ProductQ_normalizedLog_le_closedForm_sub_one (T := T) hQ0prod hQtopprod hH0 hHtop

/-- a1LocalQLog is the degree times qhatLogReadout. -/
theorem a1LocalQLog_eq_degree_qhatLogReadout (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    a1LocalQLog T b = (s1915LocalDegree T b : ℝ) * qhatLogReadout T b := by
  unfold a1LocalQLog qhatLogReadout
  have hdpos : (0 : ℝ) < (s1915LocalDegree T b : ℝ) := by
    exact_mod_cast local_degree_pos (T := T) (b := b)
  field_simp [hdpos.ne']
end LeanFormal.IUT.XiFPaper.Mzk1P0QThetaReadoutCorrespondenceActual
end