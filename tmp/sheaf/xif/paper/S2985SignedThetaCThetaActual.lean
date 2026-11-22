import tmp.sheaf.xif.paper.S2956CThetaPaperUpperActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2956CThetaPaperUpperActual
open LeanFormal.IUT.XiFPaper.S2953CThetaFromCertificateActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2985SignedThetaCThetaActual

/-- The signed theta/CTheta carrier: the finite certificate's signed theta and
signed q, the actual signed q, and the paper CTheta value, together with the
identifications that make the paper value comparable with the certificate.

`htheta` and `hqAbsLog` are not redundant data: the certificate only stores
`thetaSigned`/`qSigned`, while the paper value is defined from the actual
`q` and theta log-volume, so these two bridges are exactly what connects the
certificate fields to `CThetaPaper` (they are the S2953 field `htheta` and
the definitional `qAbsLog = |log q|`). -/
structure S2985SignedThetaCarrier (label : Type) [Fintype label]
    (l : PrimeGeFive) where
  certificate : StepXIFiniteCertificate label
  q : Real
  CThetaPaper : Real
  thetaLogVolume : Real
  qAbsLog : Real
  htheta : certificate.thetaSigned = thetaLogVolume
  hqAbsLog : qAbsLog = |Real.log q|
  hCTheta : CThetaPaper = thetaLogVolume / qAbsLog
  hupper : thetaLogVolume <= CThetaPaper * qAbsLog
  hqAbs : |Real.log q| = -certificate.qSigned

/-- The S2953 upper certificate fills the signed theta carrier: the actual q is
carried over, `qAbsLog` is its absolute log, the paper CTheta value is
identified with the certificate theta log-volume through S2956's exact-value
theorem and the S2953 `htheta` field, and the signed bridge `hqAbs` is
S2953's `hqAbs`. -/
noncomputable def S2985SignedThetaCarrier.ofCertificate
    {label : Type} [Fintype label] (l : PrimeGeFive)
    (C : S2953CThetaUpperCertificate label l) :
    S2985SignedThetaCarrier label l where
  certificate := C.certificate
  q := C.q
  CThetaPaper :=
    LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual.CThetaPaper
      l C.logQ C.dmod C.dFpd C.fFpd C.eStar C.etaPrm
  thetaLogVolume := C.thetaLogVolume
  qAbsLog := |Real.log C.q|
  htheta := C.htheta
  hqAbsLog := rfl
  hCTheta := by
    have hqpos : 0 < |Real.log C.q| := by
      rw [C.hqAbs]
      exact C.certificate.q_positive
    rw [S2956_CThetaPaper_eq_thetaSigned_div l C hqpos, C.htheta]
  hupper := C.hupper
  hqAbs := C.hqAbs

/-- Signed theta/q identity: the certificate thetaSigned over -qSigned equals
the carried theta log-volume over the absolute log of the actual q. -/
theorem S2985_signedTheta_eq_qSigned (label : Type) [Fintype label]
    (l : PrimeGeFive) (C : S2985SignedThetaCarrier label l) :
    C.certificate.thetaSigned / (-C.certificate.qSigned) =
      C.thetaLogVolume / C.qAbsLog := by
  rw [C.htheta, C.hqAbsLog, C.hqAbs]

/-- Actual value of the paper CTheta: it is the carried theta log-volume divided
by the absolute log of the actual q. -/
theorem S2985_CThetaPaper_eq_thetaLogVolume_div
    (label : Type) [Fintype label] (l : PrimeGeFive)
    (C : S2985SignedThetaCarrier label l) :
    C.CThetaPaper = C.thetaLogVolume / C.qAbsLog :=
  C.hCTheta

/-- Actual value of the paper CTheta from the certificate itself:
CThetaPaper = thetaSigned / (-qSigned), using the bridge fields `htheta`,
`hqAbsLog`, and `hqAbs`. -/
theorem S2985_CThetaPaper_eq_thetaSigned_div
    (label : Type) [Fintype label] (l : PrimeGeFive)
    (C : S2985SignedThetaCarrier label l) :
    C.CThetaPaper = C.certificate.thetaSigned / (-C.certificate.qSigned) := by
  rw [C.hCTheta, C.htheta, C.hqAbsLog, C.hqAbs]

#check S2985SignedThetaCarrier
#check S2985SignedThetaCarrier.ofCertificate
#check S2985_signedTheta_eq_qSigned
#check S2985_CThetaPaper_eq_thetaLogVolume_div
#check S2985_CThetaPaper_eq_thetaSigned_div
#print axioms S2985SignedThetaCarrier.ofCertificate
#print axioms S2985_signedTheta_eq_qSigned
#print axioms S2985_CThetaPaper_eq_thetaLogVolume_div
#print axioms S2985_CThetaPaper_eq_thetaSigned_div

end LeanFormal.IUT.XiFPaper.S2985SignedThetaCThetaActual
end
