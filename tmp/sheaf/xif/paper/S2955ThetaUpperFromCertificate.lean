import tmp.sheaf.xif.paper.S2951ThetaSignedActual
import tmp.sheaf.xif.paper.S2953CThetaFromCertificateActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2951ThetaSignedActual
open LeanFormal.IUT.XiFPaper.S2953CThetaFromCertificateActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2955ThetaUpperFromCertificate

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
local instance : Fact (Nat.Prime l.value) := ⟨l.prime⟩

/-- Actual hupper from the certificate: the certificate identity
CThetaPaper = thetaLogVolume / |log q| gives the upper bound by multiplying
by |log q|.  The certificate hupper field is not used. -/
theorem S2955_hupper_from_certificate
    {label : Type} [Fintype label]
    (C : S2953CThetaUpperCertificate label l)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hTheta : S2951ThetaSigned v R n = C.thetaLogVolume)
    (hq : S2951QParameter l = C.q) :
    S2951ThetaSigned v R n ≤
      CThetaPaper l C.logQ C.dmod C.dFpd C.fFpd C.eStar C.etaPrm *
        |Real.log (S2951QParameter l)| := by
  rw [hTheta, hq, C.hCTheta]
  have hqpos : |Real.log C.q| ≠ 0 := by
    rw [C.hqAbs]
    exact ne_of_gt C.certificate.q_positive
  field_simp [hqpos]
  exact le_rfl

/-- Actual consumer: the certificate-derived hupper plus the certificate
lower inclusion gives -1 <= CThetaPaper. -/
theorem S2955_CThetaPaper_lower_bound
    {label : Type} [Fintype label]
    (C : S2953CThetaUpperCertificate label l)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hTheta : S2951ThetaSigned v R n = C.thetaLogVolume)
    (hq : S2951QParameter l = C.q)
    (hqne : Real.log (S2951QParameter l) ≠ 0) :
    -1 ≤ CThetaPaper l C.logQ C.dmod C.dFpd C.fFpd C.eStar C.etaPrm := by
  have hupper := S2955_hupper_from_certificate C v R n hTheta hq
  have hincl : -|Real.log (S2951QParameter l)| ≤ S2951ThetaSigned v R n := by
    rw [hTheta, hq, C.hqAbs]
    simpa [C.htheta] using C.certificate.q_le_theta
  exact S2951_to_S2715_lowerBound hqne hincl hupper

#check S2955_hupper_from_certificate
#check S2955_CThetaPaper_lower_bound
#print axioms S2955_hupper_from_certificate
#print axioms S2955_CThetaPaper_lower_bound

end LeanFormal.IUT.XiFPaper.S2955ThetaUpperFromCertificate
end
