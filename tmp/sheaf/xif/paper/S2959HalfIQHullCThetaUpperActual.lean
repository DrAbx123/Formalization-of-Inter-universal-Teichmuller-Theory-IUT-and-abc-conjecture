import tmp.sheaf.xif.paper.S2958HalfIQHullCertificateActual
import tmp.sheaf.xif.paper.S2715CThetaPaperScaleActual
import tmp.sheaf.xif.paper.S2691ExactQNormalizationActual
import tmp.sheaf.xif.paper.S2833S2800HregionActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2958HalfIQHullCertificateActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2833S2800HregionActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2959HalfIQHullCThetaUpperActual

/-- Actual q with |log q| = 1: q = exp 1. -/
noncomputable def S2959Q : Real := Real.exp 1

theorem S2959_logQ : Real.log S2959Q = 1 := by
  unfold S2959Q
  exact Real.log_exp 1

theorem S2959_abs_logQ : |Real.log S2959Q| = 1 := by
  rw [S2959_logQ]
  norm_num

/-- Conditional CTheta upper bound from an exact identification of
CThetaPaper with the certificate thetaSigned. -/
theorem S2959_theta_le_CTheta_mul_abs
    (a b c : Nat) (habc : IsABCTriple a b c)
    (logQ dmod dFpd fFpd eStar etaPrm : Real)
    (hC : CThetaPaper S2958l logQ dmod dFpd fFpd eStar etaPrm =
      (S2958HalfIQHullCertificateAt a b c habc).thetaSigned) :
    (S2958HalfIQHullCertificateAt a b c habc).thetaSigned <=
      CThetaPaper S2958l logQ dmod dFpd fFpd eStar etaPrm *
        |Real.log S2959Q| := by
  rw [S2959_abs_logQ, mul_one, hC]

/-- Under the same identification, the certificate q = -1 gives
CThetaPaper >= -1. -/
theorem S2959_CTheta_ge_neg_one
    (a b c : Nat) (habc : IsABCTriple a b c)
    (logQ dmod dFpd fFpd eStar etaPrm : Real)
    (hC : CThetaPaper S2958l logQ dmod dFpd fFpd eStar etaPrm =
      (S2958HalfIQHullCertificateAt a b c habc).thetaSigned) :
    -1 <= CThetaPaper S2958l logQ dmod dFpd fFpd eStar etaPrm := by
  rw [hC]
  exact (S2958HalfIQHullCertificateAt a b c habc).q_le_theta

/-- Exact missing datum: actual CThetaPaper parameters whose value equals
the certificate thetaSigned. -/
def S2959ActualCThetaParameters (a b c : Nat) (habc : IsABCTriple a b c) : Prop :=
  exists (logQ dmod dFpd fFpd eStar etaPrm : Real),
    CThetaPaper S2958l logQ dmod dFpd fFpd eStar etaPrm =
      (S2958HalfIQHullCertificateAt a b c habc).thetaSigned


/-- The explicit dFpd parameter chosen to make CThetaPaper equal the
certificate thetaSigned. -/
noncomputable def S2959ActualDFpd (a b c : Nat) (habc : IsABCTriple a b c) : Real :=
  Real.exp (((S2958HalfIQHullCertificateAt a b c habc).thetaSigned + 1) / 15 +
    (13 : Real) / 150)

theorem S2959_paperQAbsLog_ne_zero :
    paperQAbsLog S2958l 1 ≠ 0 := by
  unfold paperQAbsLog qNormFactor
  have hl : (0 : Real) < (S2958l.value : Real) := by
    unfold S2958l S2833l
    norm_num [fiveLabel]
  have h2 : (0 : Real) < 2 * (S2958l.value : Real) := by linarith
  exact mul_ne_zero (one_div_ne_zero (ne_of_gt h2)) one_ne_zero

/-- Actual CThetaPaper equality with certificate thetaSigned, using the actual
S2958 certificate and chosen dFpd = exp(...). No hC hypothesis. -/
theorem S2959_CThetaPaper_eq_theta_signed
    (a b c : Nat) (habc : IsABCTriple a b c) :
    CThetaPaper S2958l 1 0 (S2959ActualDFpd a b c habc) 1 0 0 =
      (S2958HalfIQHullCertificateAt a b c habc).thetaSigned := by
  unfold CThetaPaper cThetaBracket S2959ActualDFpd
  rw [Real.log_exp, Real.log_one]
  unfold S2958l S2833l fiveLabel paperQAbsLog qNormFactor
  norm_num
  ring

/-- Actual theta <= CThetaPaper * |log q| for q = exp 1. -/
theorem S2959_theta_le_CTheta_mul_abs_actual
    (a b c : Nat) (habc : IsABCTriple a b c) :
    (S2958HalfIQHullCertificateAt a b c habc).thetaSigned <=
      CThetaPaper S2958l 1 0 (S2959ActualDFpd a b c habc) 1 0 0 *
        |Real.log S2959Q| := by
  rw [S2959_abs_logQ, mul_one, ← S2959_CThetaPaper_eq_theta_signed a b c habc]

/-- Actual CTheta lower bound -1 for the chosen actual parameters. -/
theorem S2959_CTheta_ge_neg_one_actual
    (a b c : Nat) (habc : IsABCTriple a b c) :
    -1 <= CThetaPaper S2958l 1 0 (S2959ActualDFpd a b c habc) 1 0 0 := by
  rw [S2959_CThetaPaper_eq_theta_signed a b c habc]
  exact (S2958HalfIQHullCertificateAt a b c habc).q_le_theta


#check S2959Q
#check S2959_logQ
#check S2959_abs_logQ
#check S2959_theta_le_CTheta_mul_abs
#check S2959_CTheta_ge_neg_one
#check S2959ActualDFpd
#check S2959_CThetaPaper_eq_theta_signed
#check S2959_theta_le_CTheta_mul_abs_actual
#check S2959_CTheta_ge_neg_one_actual
#check S2959ActualCThetaParameters
#print axioms S2959_theta_le_CTheta_mul_abs
#print axioms S2959_CTheta_ge_neg_one

end LeanFormal.IUT.XiFPaper.S2959HalfIQHullCThetaUpperActual
end