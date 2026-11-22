import tmp.sheaf.xif.paper.Mzk1CThetaToHCor312Actual
import tmp.sheaf.xif.paper.S2953CThetaFromCertificateActual
import tmp.sheaf.xif.paper.Mzk1IVThm110Actual
import Mathlib.Tactic
/-! Actual hCor312 from the Step-XI finite certificate upper.

The remaining donor is a producer of `S2953CThetaUpperCertificate` from the actual
same-source Cor 3.12 / Box / arithmetic data.  This file wires such a certificate
(its `hupper : thetaLogVolume <= CThetaPaper * |log q|`) to hCor312, so the missing
object is a single explicit producer, not a hidden assumption. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312Actual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2953CThetaFromCertificateActual
open LeanFormal.IUT.XiFPaper.Mzk1CThetaToHCor312Actual
/-- hCor312 from an actual Step-XI certificate plus the term identifications
`T.l = l.value`, `logDFpd = log dFpd`, `logFFpd = log fFpd`, and logQ data. -/
theorem hCor312_of_actual_certificate
    {label : Type} [Fintype label]
    (T : Thm110DisplayTerms) (l : PrimeGeFive) (dFpd fFpd : Real)
    (C : S2953CThetaUpperCertificate label l)
    (hqne : Real.log C.q ≠ 0)
    (hlogQpos : 0 < C.logQ)
    (hL : T.l = (l.value : Real))
    (hD : T.logDFpd = Real.log dFpd) (hF : T.logFFpd = Real.log fFpd)
    (hlogQ : T.logQ = C.logQ)
    (hdmod : T.dmod = C.dmod)
    (hdFpd : dFpd = C.dFpd) (hfFpd : fFpd = C.fFpd)
    (heStar : T.eStar = C.eStar) (hetaPrm : T.etaPrm = C.etaPrm)
    (hlogQposT : 0 < T.logQ) :
    thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T := by
  have hC : -1 ≤ CThetaPaper l T.logQ T.dmod dFpd fFpd T.eStar T.etaPrm := by
    simpa [hlogQ, hdmod, hdFpd, hfFpd, heStar, hetaPrm]
      using S2953_CThetaPaper_lower_bound l C hqne
  exact cTheta_to_hCor312 T l dFpd fFpd hL hD hF hlogQposT hC
/-- Exact first missing donor: a producer of `S2953CThetaUpperCertificate` from
the actual same-source Cor 3.12 / Box / arithmetic data (in particular the theta-hull
upper `thetaLogVolume <= CThetaPaper * |log q|`). -/
def missingCertificateProducer : List String :=
  [ "construct StepXIFiniteCertificate / S2953CThetaUpperCertificate from actual theta hull",
    "prove thetaLogVolume <= CThetaPaper * |log q| from Box (11) plus q normalization",
    "prove |log q| = -qSigned and CThetaPaper = thetaLogVolume / |log q| from actual data" ]
theorem missingCertificateProducer_length : missingCertificateProducer.length = 3 := rfl
#check hCor312_of_actual_certificate
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312Actual
end
