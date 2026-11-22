import tmp.sheaf.xif.paper.S2990ActualDFpdActual
import tmp.sheaf.xif.paper.S2966AbsNormJEqRadActual
import tmp.sheaf.xif.paper.S2715CThetaPaperScaleActual
import tmp.sheaf.xif.paper.S2691ExactQNormalizationActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2990ActualDFpdActual
open LeanFormal.IUT.XiFPaper.S2966AbsNormJEqRadActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S3045CThetaPaperNonnegCounterexample

/-- The actual fFpd at (1,2,3) is positive. -/
theorem S3045_FFpd_pos : 0 < S2990FFpd 1 2 3 := by
  unfold S2990FFpd
  have habc : IsABCTriple 1 2 3 :=
    ⟨Nat.one_pos, by norm_num, by norm_num, Nat.coprime_one_left 2⟩
  have hrad : natRadical (1 * 2 * 3) <=
      Ideal.absNorm (S2752J S2771FiveLabel 1 2 3) :=
    S2966_rad_le_absNorm 1 2 3 habc
  have h6 : 0 < natRadical (1 * 2 * 3) := natRadical_pos (1 * 2 * 3)
  have hpos : 0 < Ideal.absNorm (S2752J S2771FiveLabel 1 2 3) :=
    lt_of_lt_of_le h6 hrad
  exact_mod_cast hpos

/-- The actual dFpd is positive. -/
theorem S3045_DFpd_pos : 0 < S2990DFpd := S2990DFpd_pos

/-- A concrete logQ making CThetaPaper negative. -/
noncomputable def S3045LogQ : Real :=
  max 1 ((Real.log S2990DFpd + Real.log (S2990FFpd 1 2 3)) /
    (13 / 150 : Real) + 1)

theorem S3045_logQ_pos : 0 < S3045LogQ := by
  unfold S3045LogQ
  exact lt_of_lt_of_le zero_lt_one (le_max_left 1 _)

/-- CThetaPaper at chosen logQ is negative for the actual dFpd/fFpd. -/
theorem S3045_CThetaPaper_neg :
    CThetaPaper fiveLabel S3045LogQ 0 S2990DFpd (S2990FFpd 1 2 3) 0 0 < 0 := by
  unfold CThetaPaper cThetaBracket S3045LogQ paperQAbsLog qNormFactor
  have hlogQ1 : (1 : Real) <= max 1 ((Real.log S2990DFpd + Real.log (S2990FFpd 1 2 3)) /
      (13 / 150 : Real) + 1) := le_max_left _ _
  have hlogQ2 : (Real.log S2990DFpd + Real.log (S2990FFpd 1 2 3)) /
      (13 / 150 : Real) + 1 <=
      max 1 ((Real.log S2990DFpd + Real.log (S2990FFpd 1 2 3)) /
        (13 / 150 : Real) + 1) := le_max_right _ _
  have hQpos : 0 < (1 / (2 * (fiveLabel.value : Real))) *
      max 1 ((Real.log S2990DFpd + Real.log (S2990FFpd 1 2 3)) /
        (13 / 150 : Real) + 1) := by
    have h5 : (0 : Real) < (fiveLabel.value : Real) := by norm_num [fiveLabel]
    have h2 : (0 : Real) < 2 * (fiveLabel.value : Real) := by linarith
    have hfac : (0 : Real) < 1 / (2 * (fiveLabel.value : Real)) := by positivity
    exact mul_pos hfac (lt_of_lt_of_le zero_lt_one hlogQ1)
  have hB : (1 + 12 * 0 / (fiveLabel.value : Real)) *
        (Real.log S2990DFpd + Real.log (S2990FFpd 1 2 3)) +
      10 * (0 * (fiveLabel.value : Real) + 0) -
      (1 / 6) * (1 - 12 / ((fiveLabel.value : Real)) ^ 2) *
        max 1 ((Real.log S2990DFpd + Real.log (S2990FFpd 1 2 3)) /
          (13 / 150 : Real) + 1) < 0 := by
    have hc : (0 : Real) < 13 / 150 := by norm_num
    have hkey : (Real.log S2990DFpd + Real.log (S2990FFpd 1 2 3)) -
        (1 / 6) * (1 - 12 / ((fiveLabel.value : Real)) ^ 2) *
          max 1 ((Real.log S2990DFpd + Real.log (S2990FFpd 1 2 3)) /
            (13 / 150 : Real) + 1) < 0 := by
      have h5 : (fiveLabel.value : Real) = 5 := by norm_num [fiveLabel]
      have hcoef : (1 / 6) * (1 - 12 / ((fiveLabel.value : Real)) ^ 2) =
          (13 / 150 : Real) := by rw [h5]; norm_num
      rw [hcoef]
      have hlin : (13 / 150 : Real) *
          max 1 ((Real.log S2990DFpd + Real.log (S2990FFpd 1 2 3)) /
            (13 / 150 : Real) + 1) >=
          (13 / 150 : Real) *
            ((Real.log S2990DFpd + Real.log (S2990FFpd 1 2 3)) /
              (13 / 150 : Real) + 1) := by
        exact mul_le_mul_of_nonneg_left hlogQ2 (le_of_lt hc)
      nlinarith
    simpa [zero_mul, zero_add, mul_one, add_zero] using hkey
  have hfac : 0 < ((fiveLabel.value : Real) + 1) / 4 / ((1 / (2 *
      (fiveLabel.value : Real))) *
      max 1 ((Real.log S2990DFpd + Real.log (S2990FFpd 1 2 3)) /
        (13 / 150 : Real) + 1)) := by
    have h5 : (0 : Real) < (fiveLabel.value : Real) := by norm_num [fiveLabel]
    have hnum : (0 : Real) < ((fiveLabel.value : Real) + 1) / 4 := by positivity
    exact div_pos hnum hQpos
  have hmul : ((fiveLabel.value : Real) + 1) / 4 / ((1 / (2 *
      (fiveLabel.value : Real))) *
      max 1 ((Real.log S2990DFpd + Real.log (S2990FFpd 1 2 3)) /
        (13 / 150 : Real) + 1)) *
      ((1 + 12 * 0 / (fiveLabel.value : Real)) *
        (Real.log S2990DFpd + Real.log (S2990FFpd 1 2 3)) +
      10 * (0 * (fiveLabel.value : Real) + 0) -
      (1 / 6) * (1 - 12 / ((fiveLabel.value : Real)) ^ 2) *
        max 1 ((Real.log S2990DFpd + Real.log (S2990FFpd 1 2 3)) /
          (13 / 150 : Real) + 1)) < 0 :=
    mul_neg_of_pos_of_neg hfac hB
  linarith

#check S3045_FFpd_pos
#check S3045_DFpd_pos
#check S3045_CThetaPaper_neg

end LeanFormal.IUT.XiFPaper.S3045CThetaPaperNonnegCounterexample
end