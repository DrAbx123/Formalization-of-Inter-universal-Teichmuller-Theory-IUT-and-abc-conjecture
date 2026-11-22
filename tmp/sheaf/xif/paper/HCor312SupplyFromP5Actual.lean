/- hCor312 supply from actual P5/actual certificate. -/
import tmp.sheaf.xif.paper.Mzk1G1P8DisplaySupplyActual
import tmp.sheaf.xif.paper.Mzk1P5InequalityCarrierGlueActual
import tmp.sheaf.xif.paper.S2953CThetaFromCertificateActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.HCor312SupplyFromP5Actual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1P8DisplaySupplyActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.S2953CThetaFromCertificateActual
open LeanFormal.IUT.XiFPaper.Mzk1P5InequalityCarrierGlueActual
/-- Actual hCor312 supply from an actual S2953 CTheta certificate and the
actual display-term identifications. -/
theorem hCor312SupplyFromP5
    {label : Type} [Fintype label]
    (T : Thm110DisplayTerms) (l : PrimeGeFive) (dFpd fFpd : Real)
    (C : S2953CThetaUpperCertificate label l)
    (hqne : Real.log C.q ≠ 0) (hlogQpos : 0 < C.logQ)
    (hL : T.l = (l.value : Real))
    (hD : T.logDFpd = Real.log dFpd) (hF : T.logFFpd = Real.log fFpd)
    (hlogQ : T.logQ = C.logQ) (hdmod : T.dmod = C.dmod)
    (hdFpd : dFpd = C.dFpd) (hfFpd : fFpd = C.fFpd)
    (heStar : T.eStar = C.eStar) (hetaPrm : T.etaPrm = C.etaPrm)
    (hlogQposT : 0 < T.logQ) :
    thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T :=
  g1p8_hCor312_supply T l dFpd fFpd C hqne hlogQpos hL hD hF hlogQ hdmod hdFpd hfFpd heStar hetaPrm hlogQposT
#check hCor312SupplyFromP5
end LeanFormal.IUT.XiFPaper.HCor312SupplyFromP5Actual
end
