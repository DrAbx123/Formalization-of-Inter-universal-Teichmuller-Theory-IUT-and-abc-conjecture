import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealSignedLogVolume

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2978SignedThetaCarrierActual

variable {l : PrimeGeFive} {V : Type*}
variable (I : Theorem311Source.OriginalInput l V)

/-- Signed theta carrier: the signed finite certificate together with the
signed hull cap.  Only signed hull data is used; no raw `sourceHullVolume`. -/
structure S2978SignedThetaCarrier (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) where
  certificate : StepXIFiniteCertificate (SignedLabel l.value)
  signedHullVolume : Real
  htheta_zero : certificate.thetaSigned = 0
  hq_le : certificate.qSigned <= signedHullVolume
  hq_neg : certificate.qSigned < 0
  hhull_le_theta : signedHullVolume <= certificate.thetaSigned

noncomputable def S2978SignedThetaCarrier.ofSignedHull
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (qSigned : Real)
    (hq : qSigned <= I.sourceSignedHullLogVolume v R n) (hqneg : qSigned < 0) :
    S2978SignedThetaCarrier I v R n where
  certificate := I.sourceSignedHullCertificate v R n qSigned hq hqneg
  signedHullVolume := I.sourceSignedHullLogVolume v R n
  htheta_zero := rfl
  hq_le := hq
  hq_neg := hqneg
  hhull_le_theta := I.sourceSignedHullLogVolume_nonpos v R n

theorem S2978_signedThetaCarrier_theta_nonpos
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (C : S2978SignedThetaCarrier I v R n) :
    C.certificate.thetaSigned <= 0 :=
  C.htheta_zero.le

#check S2978SignedThetaCarrier
#check S2978SignedThetaCarrier.ofSignedHull
#check S2978_signedThetaCarrier_theta_nonpos
#print axioms S2978SignedThetaCarrier.ofSignedHull
#print axioms S2978_signedThetaCarrier_theta_nonpos

end LeanFormal.IUT.XiFPaper.S2978SignedThetaCarrierActual
end
