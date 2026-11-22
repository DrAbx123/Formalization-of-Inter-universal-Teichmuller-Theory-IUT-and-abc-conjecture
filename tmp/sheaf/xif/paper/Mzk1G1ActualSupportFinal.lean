/- Actual G1 support: Fermat cover, actual Thm 1.10 display terms, actual N5
condition, and hCor312 supply wrapper. -/
import tmp.sheaf.xif.paper.Mzk1G1P8DisplaySupplyActual
import tmp.sheaf.xif.paper.Mzk1G1P8CertificateActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1ActualSupportFinal

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8DisplaySupplyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8CertificateActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.S3013QSideSignedValueCondition
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312Actual

/-- Actual G1 Fermat cover. -/
noncomputable def g1SupportCover : FermatCoverData ℂ := g1ActualCover

/-- Actual Thm 1.10 display terms from actual IV data. -/
noncomputable def g1SupportTerms (A : ActualThm110Data) : Thm110DisplayTerms :=
  g1p8DisplayTerms A

/-- Actual N5 q-side signed condition. -/
theorem g1Support_n5 {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] :
    qSideSignedValueCondition (S3013QPilot T) (S3013QSigned T) :=
  actual_n5_qSideSignedValueCondition T

/-- Actual hCor312 supply wrapper from an actual S2953 certificate. -/
theorem g1Support_hCor312_supply
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
  g1p8_hCor312_supply T l dFpd fFpd C hqne hlogQpos hL hD hF hlogQ hdmod
    hdFpd hfFpd heStar hetaPrm hlogQposT

#check g1SupportCover
#check g1SupportTerms
#check g1Support_n5
#check g1Support_hCor312_supply

end LeanFormal.IUT.XiFPaper.Mzk1G1ActualSupportFinal
end
