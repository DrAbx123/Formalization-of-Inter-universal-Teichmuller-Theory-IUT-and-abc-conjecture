import tmp.sheaf.xif.paper.S2715CThetaPaperScaleActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CertificateCThetaTransfer
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2953CThetaFromCertificateActual

/-- The certificate-side upper input for CThetaPaper: thetaSigned is identified
with the actual theta log-volume, and CThetaPaper is identified with the
certificate coefficient. -/
structure S2953CThetaUpperCertificate
    (label : Type) [Fintype label]
    (l : PrimeGeFive) where
  certificate : StepXIFiniteCertificate label
  q : Real
  logQ : Real
  dmod : Real
  dFpd : Real
  fFpd : Real
  eStar : Real
  etaPrm : Real
  thetaLogVolume : Real
  htheta : certificate.thetaSigned = thetaLogVolume
  hqAbs : |Real.log q| = -certificate.qSigned
  hCTheta : CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm =
    (thetaLogVolume) / |Real.log q|
  hupper : thetaLogVolume <=
    CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm * |Real.log q|

/-- The certificate upper input yields the paper lower bound
-1 <= CThetaPaper. -/
theorem S2953_CThetaPaper_lower_bound
    {label : Type} [Fintype label]
    (l : PrimeGeFive) (C : S2953CThetaUpperCertificate label l)
    (hqne : Real.log C.q ≠ 0) :
    -1 <= CThetaPaper l C.logQ C.dmod C.dFpd C.fFpd C.eStar C.etaPrm := by
  have hc : C.certificate.thetaSigned <=
      CThetaPaper l C.logQ C.dmod C.dFpd C.fFpd C.eStar C.etaPrm *
        |Real.log C.q| := by
    rw [C.htheta]
    exact C.hupper
  exact cTheta_lower_bound_of_finiteCertificate C.certificate C.hqAbs hc

/-- Consumer form with thetaSigned upper rewritten directly in CThetaPaper. -/
theorem S2953_CThetaPaper_upper_consumer
    {label : Type} [Fintype label]
    (l : PrimeGeFive) (C : S2953CThetaUpperCertificate label l)
    (hqne : Real.log C.q ≠ 0) :
    C.certificate.thetaSigned <=
        CThetaPaper l C.logQ C.dmod C.dFpd C.fFpd C.eStar C.etaPrm *
          |Real.log C.q|
      ∧ -1 <= CThetaPaper l C.logQ C.dmod C.dFpd C.fFpd C.eStar C.etaPrm := by
  constructor
  · rw [C.htheta]
    exact C.hupper
  · exact S2953_CThetaPaper_lower_bound l C hqne

#check S2953CThetaUpperCertificate
#check S2953_CThetaPaper_lower_bound
#check S2953_CThetaPaper_upper_consumer
#print axioms S2953_CThetaPaper_lower_bound

end LeanFormal.IUT.XiFPaper.S2953CThetaFromCertificateActual
end