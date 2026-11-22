import tmp.sheaf.xif.paper.S3047bActualParameterHscalarAttempt
import tmp.sheaf.xif.paper.S2990ActualDFpdActual
import tmp.sheaf.xif.paper.S2966AbsNormJEqRadActual
import tmp.sheaf.xif.paper.S3043LocalHaarVolumeSignActual
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3047bActualParameterHscalarAttempt
open LeanFormal.IUT.XiFPaper.S2990ActualDFpdActual
open LeanFormal.IUT.XiFPaper.S2966AbsNormJEqRadActual
open LeanFormal.IUT.XiFPaper.S3043LocalHaarVolumeSignActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3048MeasureLowerBoundActual

variable {l : PrimeGeFive} {V : Type*}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Actual fFpd is at least 2 for every ABC triple. -/
theorem S3048_FFpd_ge_two (a b c : Nat) (habc : IsABCTriple a b c) :
    (2 : Real) <= S2990FFpd a b c := by
  unfold S2990FFpd
  have hprod : 2 <= a * b * c := by
    rcases habc with ⟨ha, hb, hsum, _⟩
    have hc : 2 <= c := by omega
    have h1 : 1 <= a * b := by nlinarith [Nat.one_le_iff_ne_zero.mpr (ne_of_gt ha), Nat.one_le_iff_ne_zero.mpr (ne_of_gt hb)]
    nlinarith
  have hrad : 2 <= natRadical (a * b * c) := by
    rw [Nat.two_le_radical_iff]
    exact hprod
  have hle : natRadical (a * b * c) <=
      Ideal.absNorm (S2752J S2771FiveLabel a b c) :=
    S2966_rad_le_absNorm a b c habc
  exact_mod_cast le_trans hrad hle

/-- Actual dFpd is at least 1. -/
theorem S3048_DFpd_ge_one : (1 : Real) <= S2990DFpd := by
  have hnat : 0 < Ideal.absNorm (differentIdeal ℤ S2990R) := by
    have h := S2990DFpd_pos
    unfold S2990DFpd at h
    exact_mod_cast h
  have hnat1 : (1 : Nat) <= Ideal.absNorm (differentIdeal ℤ S2990R) :=
    Nat.one_le_iff_ne_zero.mpr (ne_of_gt hnat)
  unfold S2990DFpd
  exact_mod_cast hnat1

/-- The actual CThetaPaper at logQ = 1 is nonnegative for every ABC triple. -/
theorem S3048_CTheta_nonneg (a b c : Nat) (habc : IsABCTriple a b c) :
    0 <= S3047bCTheta a b c := by
  unfold S3047bCTheta
  have hD : 0 <= Real.log S2990DFpd := Real.log_nonneg S3048_DFpd_ge_one
  have hF : Real.log (2 : Real) <= Real.log (S2990FFpd a b c) :=
    Real.log_le_log (by norm_num) (S3048_FFpd_ge_two a b c habc)
  have hlog2 : (0.6931471803 : Real) < Real.log 2 := Real.log_two_gt_d9
  have hbracket : (0 : Real) <=
      Real.log S2990DFpd + Real.log (S2990FFpd a b c) - 13 / 150 := by
    linarith
  have hfac : CThetaPaper fiveLabel 1 0 S2990DFpd (S2990FFpd a b c) 0 0 =
      15 * (Real.log S2990DFpd + Real.log (S2990FFpd a b c) - 13 / 150) - 1 := by
    unfold CThetaPaper cThetaBracket paperQAbsLog qNormFactor
    norm_num [fiveLabel]
  rw [hfac]
  nlinarith

/-- Exact measure lower bound, proved from CThetaPaper nonnegativity and V>=0. -/
theorem S3048_measureLowerBound (a b c : Nat) (habc : IsABCTriple a b c) :
    S3047bMissingMeasureLowerBound C3 a b c := by
  unfold S3047bMissingMeasureLowerBound
  have hC : 0 <= S3047bCTheta a b c := S3048_CTheta_nonneg a b c habc
  have hQ : 0 <= S3047bQ := by
    unfold S3047bQ paperQAbsLog qNormFactor
    positivity
  have hprod : 0 <= S3047bCTheta a b c * S3047bQ := mul_nonneg hC hQ
  have hV : 0 <= actualC3LogShellTensorLogVolume C3 := S3043_logVolume_nonneg C3
  linarith

#check S3048_CTheta_nonneg
#check S3048_measureLowerBound
#print axioms S3048_CTheta_nonneg
#print axioms S3048_measureLowerBound

end LeanFormal.IUT.XiFPaper.S3048MeasureLowerBoundActual
end