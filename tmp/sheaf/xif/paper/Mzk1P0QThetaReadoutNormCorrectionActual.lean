/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.three_gap_closure_20261114.QhatHaarScalingReuse
import tmp.sheaf.xif.paper.Mzk1P2QNativeReadingCorrectedActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.Mzk1P0QThetaReadoutCorrespondenceActual
import tmp.sheaf.xif.paper.BadPlacePaperTargetStrictActual
import tmp.sheaf.xif.paper.Mzk1P0QThetaReadoutCorrespondenceActual
import Mathlib.Tactic
/-! # Norm-instance correction between qhatLogReadout and the paper q readout

The exact identity is (under the norm-instance agreement):
  qhatLogReadout - paperQSignedReadout = log(qVFamNormRatio).
Thus a paper-faithful Q<=Theta cannot silently drop this correction.  We record
the exact identity, its weighted global form, and the correction-zero cases.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0QThetaReadoutNormCorrectionActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P2QNativeReadingCorrectedActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1P0QThetaReadoutCorrespondenceActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperTargetStrictActual
open LeanFormal.IUT.XiFPaper.Mzk1P0QThetaReadoutCorrespondenceActual
open LeanFormal.IUT.ThreeGapClosure20261114
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open scoped BigOperators
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
abbrev qhatLogReadout (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Real :=
  Mzk1P0QThetaReadoutCorrespondenceActual.qhatLogReadout (T := T) (b := b)
/-- Paper q signed readout as -|log raw q| = -localLogMagnitude. -/
noncomputable def paperQSignedReadout (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Real :=
  -localLogMagnitude (QPilotZeroLocusDivisorActual.qVFamily (T := T) (b := b))
/-- qhatLogReadout is log||qhat|| (root scaling). -/
theorem qhatLogReadout_eq_log_norm :
    qhatLogReadout (T := T) (b := b) = Real.log ‖c0QHat T b‖ :=
  qhat_signed_readout_eq_log_norm (T := T) (b := b)
/-- Exact norm-instance correction identity, under the P2 norm agreement. -/
theorem qhatLogReadout_sub_paperQ_eq_log_ratio
    (h : ‖c0QHat T b‖ = qVFamNormalizedNorm T b) :
    qhatLogReadout (T := T) (b := b) - paperQSignedReadout (T := T) (b := b) =
      Real.log (qVFamNormRatio T b) := by
  have hp2 := p2NativeQReading_eq_neg_log_qhat_add_ratio (T := T) b h
  rw [qhatLogReadout_eq_log_norm (T := T) (b := b)]
  unfold paperQSignedReadout
  ring_nf
  linarith [hp2]
/-- Weighted global sum of qhatLogReadout. -/
noncomputable def qhatLogReadoutGlobal (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * qhatLogReadout (T := T) (b := b)
/-- Weighted global paper q readout. -/
noncomputable def paperQSignedReadoutGlobal (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * paperQSignedReadout (T := T) (b := b)
/-- The weighted correction is the weighted sum of log ratios. -/
theorem qhatLogReadoutGlobal_sub_paperQ_eq_sum_log_ratio
    (h : ∀ b : Bad (nativePlaceSelection T),
      ‖c0QHat T b‖ = qVFamNormalizedNorm T b) :
    qhatLogReadoutGlobal (T := T) - paperQSignedReadoutGlobal (T := T) =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * Real.log (qVFamNormRatio T b) := by
  unfold qhatLogReadoutGlobal paperQSignedReadoutGlobal
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_sub, qhatLogReadout_sub_paperQ_eq_log_ratio (T := T) (b := b) (h b)]
/-- Correction vanishes pointwise under the norm agreement and ratio one. -/
theorem qhatLogReadout_eq_paperQ_of_ratio_one
    (hnorm : ‖c0QHat T b‖ = qVFamNormalizedNorm T b)
    (h : qVFamNormRatio T b = 1) :
    qhatLogReadout (T := T) (b := b) = paperQSignedReadout (T := T) (b := b) := by
  have hp2 := p2NativeQReading_eq_neg_log_qhat_add_ratio (T := T) b hnorm
  rw [h, Real.log_one] at hp2
  have hq := qhatLogReadout_eq_log_norm (T := T) (b := b)
  unfold paperQSignedReadout
  ring_nf
  linarith [hp2, hq]

/-- Degree-weighted global qhat signed log sum (consumer convention d_b=finrank). -/
noncomputable def qhatLogReadoutDegreeGlobal (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    (s1915LocalDegree T b : Real) * qhatLogReadout (T := T) (b := b)
/-- Degree-weighted global paper q signed readout. -/
noncomputable def paperQSignedReadoutDegreeGlobal (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    (s1915LocalDegree T b : Real) * paperQSignedReadout (T := T) (b := b)
/-- Degree-weighted correction identity. -/
theorem qhatLogReadoutDegreeGlobal_sub_paperQ_eq_sum_degree_log_ratio
    (h : ∀ b : Bad (nativePlaceSelection T),
      ‖c0QHat T b‖ = qVFamNormalizedNorm T b) :
    qhatLogReadoutDegreeGlobal (T := T) - paperQSignedReadoutDegreeGlobal (T := T) =
      ∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) * Real.log (qVFamNormRatio T b) := by
  unfold qhatLogReadoutDegreeGlobal paperQSignedReadoutDegreeGlobal
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_sub, qhatLogReadout_sub_paperQ_eq_log_ratio (T := T) (b := b) (h b)]
/-- Correction form: paper q <= theta minus the degree-weighted log-ratio correction. -/
theorem paperQDegree_le_closedForm_sub_one_sub_correction
    (hnorm : ∀ b : Bad (nativePlaceSelection T),
      ‖c0QHat T b‖ = qVFamNormalizedNorm T b) :
    paperQSignedReadoutDegreeGlobal (T := T) ≤
      (s1915ClosedForm T - 1) -
        ∑ b : Bad (nativePlaceSelection T),
          (s1915LocalDegree T b : Real) * Real.log (qVFamNormRatio T b) := by
  have hcorr := qhatLogReadoutDegreeGlobal_sub_paperQ_eq_sum_degree_log_ratio (T := T) hnorm
  have hbound := sum_degree_qhatLogReadout_le_closedForm_sub_one (T := T)
  unfold qhatLogReadoutDegreeGlobal at hcorr ⊢
  linarith [hcorr, hbound]
/-- S45 conditional form: under correction-free source fields and norm agreement,
paper q readout is bounded by the theta closed form. -/
theorem paperQDegree_le_closedForm_sub_one_of_fields
    (S : PaperSourceCorrectionFreeFields T)
    (hnorm : ∀ b : Bad (nativePlaceSelection T),
      ‖c0QHat T b‖ = qVFamNormalizedNorm T b) :
    paperQSignedReadoutDegreeGlobal (T := T) ≤ s1915ClosedForm T - 1 := by
  have hcorr := paperQDegree_le_closedForm_sub_one_sub_correction (T := T) hnorm
  have hzero : (∑ b : Bad (nativePlaceSelection T),
      (s1915LocalDegree T b : Real) * Real.log (qVFamNormRatio T b)) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    rw [S.normRatio_one b, Real.log_one, mul_zero]
  rw [hzero, sub_zero] at hcorr
  exact hcorr
end LeanFormal.IUT.XiFPaper.Mzk1P0QThetaReadoutNormCorrectionActual
end