import tmp.sheaf.xif.paper.S2953CThetaFromCertificateActual
import tmp.sheaf.xif.paper.S2715CThetaPaperScaleActual
import tmp.sheaf.xif.paper.S2691ExactQNormalizationActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2953CThetaFromCertificateActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2956CThetaPaperUpperActual

/-- Exact value of CThetaPaper from the certificate data: it is thetaSigned
divided by |log q|, not a separately chosen AJ. -/
theorem S2956_CThetaPaper_eq_thetaSigned_div
    {label : Type} [Fintype label]
    (l : PrimeGeFive) (C : S2953CThetaUpperCertificate label l)
    (hqpos : 0 < |Real.log C.q|) :
    CThetaPaper l C.logQ C.dmod C.dFpd C.fFpd C.eStar C.etaPrm =
      C.certificate.thetaSigned / |Real.log C.q| := by
  rw [C.hCTheta, C.htheta]

/-- Actual upper bound: CThetaPaper is at most the certificate thetaSigned
divided by the positive paper q-absolute-log. -/
theorem S2956_CThetaPaper_upper
    {label : Type} [Fintype label]
    (l : PrimeGeFive) (C : S2953CThetaUpperCertificate label l)
    (hqpos : 0 < |Real.log C.q|) :
    CThetaPaper l C.logQ C.dmod C.dFpd C.fFpd C.eStar C.etaPrm <=
      C.certificate.thetaSigned / |Real.log C.q| := by
  rw [S2956_CThetaPaper_eq_thetaSigned_div l C hqpos]

/-- Equivalent exact form after rewriting |log q| via qSigned. -/
theorem S2956_CThetaPaper_eq_neg_theta_div_qSigned
    {label : Type} [Fintype label]
    (l : PrimeGeFive) (C : S2953CThetaUpperCertificate label l)
    (hqpos : 0 < |Real.log C.q|) :
    CThetaPaper l C.logQ C.dmod C.dFpd C.fFpd C.eStar C.etaPrm =
      C.certificate.thetaSigned / (-C.certificate.qSigned) := by
  rw [S2956_CThetaPaper_eq_thetaSigned_div l C hqpos, C.hqAbs]

#check S2956_CThetaPaper_eq_thetaSigned_div
#check S2956_CThetaPaper_upper
#check S2956_CThetaPaper_eq_neg_theta_div_qSigned
#print axioms S2956_CThetaPaper_eq_thetaSigned_div
#print axioms S2956_CThetaPaper_upper

end LeanFormal.IUT.XiFPaper.S2956CThetaPaperUpperActual
end