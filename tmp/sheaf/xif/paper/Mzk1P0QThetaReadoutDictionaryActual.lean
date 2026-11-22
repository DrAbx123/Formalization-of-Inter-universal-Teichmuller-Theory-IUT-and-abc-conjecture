/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.three_gap_closure_20261114.QhatHaarScalingReuse
import tmp.sheaf.xif.paper.Mzk1P2QNativeReadingCorrectedActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.Mzk1RootImageRadiusFormulaActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import Mathlib.Tactic
/-! # q/theta readout dictionary: c_norm log p, root radius, 1/(2l)

Pointwise dictionary (all actual objects, no paperNetSlack/R37):
  qhatLogReadout = log||qhat|| = - c_norm * log p        (norm agreement)
  paperQSignedReadout = -localLogMagnitude = -|log raw q|
  c_norm * log p = localLogMagnitude - log ratio
  log(rootImageRadius) = -(c_norm/(2l)) * log p.
Thus the theta degree sum is (1/(2l)) times the q degree sum (after correction).
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0QThetaReadoutDictionaryActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.Mzk1P2QNativeReadingCorrectedActual
open LeanFormal.IUT.XiFPaper.Mzk1RootImageRadiusFormulaActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.ThreeGapClosure20261114
open LeanFormal.IUT.ArithmeticQPilotLogVolume
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
/-- Local qhat signed readout (same normalization as the root scaling). -/
noncomputable def qhatLogReadout (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Real :=
  (1 / (s1915LocalDegree T b : Real)) *
    (Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
      Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal)
/-- Under norm agreement, qhatLogReadout is the negative normalized coefficient times log p. -/
theorem qhatLogReadout_eq_neg_normalizedCoeff_log_p
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T))
    (h : ‖c0QHat T b‖ = qVFamNormalizedNorm T b) :
    qhatLogReadout T b =
      -qVFamNormalizedCoefficient T b * Real.log (qVFamTensorP T b : Real) := by
  have hq := qhat_signed_readout_eq_log_norm T b
  have hbridge := qVFamNormalizedCoefficient_mul_log_eq_neg_log_norm (T := T) (b := b)
  have hlog : Real.log ‖c0QHat T b‖ = Real.log (qVFamNormalizedNorm T b) := by rw [h]
  unfold qhatLogReadout
  linarith [hq, hlog, hbridge]
/-- Exact relation of the normalized coefficient to the paper q readout and ratio. -/
theorem normalizedCoeff_log_eq_paperQ_add_ratio
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    qVFamNormalizedCoefficient T b * Real.log (qVFamTensorP T b : Real) =
      -(-localLogMagnitude (QPilotZeroLocusDivisorActual.qVFamily (T := T) (b := b))) - Real.log (qVFamNormRatio T b) := by
  rw [qVFamNormalizedCoefficient_mul_log_eq_localLogMagnitude_sub_log_ratio (T := T) (b := b)]
  ring
/-- Root radius log relation: log r = -(c_norm/(2l)) log p. -/
theorem log_rootImageRadius_eq_neg_coeff_mul_logp_div_twoL
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T)) :
    Real.log (rootImageRadius T b : Real) =
      -(qVFamNormalizedCoefficient T b * Real.log (qVFamTensorP T b : Real)) /
        (2 * (l.value : Real)) :=
  Mzk1RootImageRadiusFormulaActual.log_rootImageRadius_eq_neg_coeff_mul_logp_div_twoL (l := l) (T := T) (b := b)
/-- Degree theta term is (1/(2l)) times the positive normalized coefficient term. -/
theorem degree_log_radius_eq_div_twoL_mul_degree_qhat
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T))
    (h : ‖c0QHat T b‖ = qVFamNormalizedNorm T b) :
    (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real) =
      (1 / (2 * (l.value : Real))) *
        ((s1915LocalDegree T b : Real) * qhatLogReadout T b) := by
  rw [log_rootImageRadius_eq_neg_coeff_mul_logp_div_twoL (T := T) (b := b)]
  rw [qhatLogReadout_eq_neg_normalizedCoeff_log_p (T := T) (b := b) h]
  ring
/-- Global theta degree sum equals 1/(2l) times the global q degree sum. -/
theorem sum_degree_log_radius_eq_div_twoL_mul_sum_degree_qhat
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (h : ∀ b : Bad (nativePlaceSelection T),
      ‖c0QHat T b‖ = qVFamNormalizedNorm T b) :
    (∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real)) =
      (1 / (2 * (l.value : Real))) *
        ∑ b : Bad (nativePlaceSelection T),
          (s1915LocalDegree T b : Real) * qhatLogReadout T b := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact degree_log_radius_eq_div_twoL_mul_degree_qhat (T := T) (b := b) (h b)

/-- Paper weight is the inverse actual completion degree, i.e. 1/[K_w:F_v];
this is NOT 1/f when e > 1. -/
theorem paperWeight_eq_inv_localCompletionDegree
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    nativeBadLocalWeight T b =
      ((localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : Nat) : Real)⁻¹ :=
  nativeBadLocalWeight_eq_inv (T := T) b
/-- Degree tower interface: d_b = n_b * [K_w:F_v].  The intermediate degree n_b is
not constructed in this file; the paper weight is 1/[K_w:F_v], not 1/d_b. -/
def DegreeTowerInterface : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    ∃ n : Nat, s1915LocalDegree T b = n * localCompletionDegree T.arithmetic (nativeBadToKPlace T b)
end LeanFormal.IUT.XiFPaper.Mzk1P0QThetaReadoutDictionaryActual
end