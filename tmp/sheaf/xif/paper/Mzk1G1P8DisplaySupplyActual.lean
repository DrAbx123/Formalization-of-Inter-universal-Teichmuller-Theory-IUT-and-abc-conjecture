/- G1/P8 actual display supply: actual G1 Fermat cover, actual Thm 1.10
display terms from ActualThm110Data, and hCor312 supply from an actual
S2953 CTheta upper certificate. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatCoverActual
import tmp.sheaf.xif.paper.Mzk1P8ActualDisplayHeightActual
import tmp.sheaf.xif.paper.Mzk1IVThm110HCor312Actual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1P8DisplaySupplyActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2953CThetaFromCertificateActual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual

/-- Actual G1 Fermat cover at n=1. -/
noncomputable def g1ActualCover : FermatCoverData ℂ :=
  fermatCoverData ℂ 1 (by norm_num)

/-- Actual Thm 1.10 display terms from actual IV data. -/
noncomputable def g1p8DisplayTerms (A : ActualThm110Data) : Thm110DisplayTerms :=
  A.toTerms

/-- Actual hCor312 supply from an actual S2953 CTheta upper certificate and the
display-term identifications. -/
theorem g1p8_hCor312_supply
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
  hCor312_of_actual_certificate T l dFpd fFpd C hqne hlogQpos hL hD hF
    hlogQ hdmod hdFpd hfFpd heStar hetaPrm hlogQposT

/-- Concrete G1/P8 display supply package: actual G1 Fermat cover, actual
display terms, and an actual hCor312 proof. -/
structure G1P8DisplaySupply (A : ActualThm110Data) where
  cover : FermatCoverData ℂ
  terms : Thm110DisplayTerms
  terms_eq : terms = g1p8DisplayTerms A
  hCor312 : thm110Lhs terms ≤ thm110Mid terms + thm110Cor312Gap terms

/-- Construct the G1/P8 display supply package from actual data and the actual
hCor312 certificate supply. -/
noncomputable def g1p8DisplaySupply
    (A : ActualThm110Data)
    (hCor312 : thm110Lhs (g1p8DisplayTerms A) ≤
      thm110Mid (g1p8DisplayTerms A) + thm110Cor312Gap (g1p8DisplayTerms A)) :
    G1P8DisplaySupply A where
  cover := g1ActualCover
  terms := g1p8DisplayTerms A
  terms_eq := rfl
  hCor312 := hCor312

#check g1ActualCover
#check g1p8DisplayTerms
#check g1p8_hCor312_supply
#check g1p8DisplaySupply

end LeanFormal.IUT.XiFPaper.Mzk1G1P8DisplaySupplyActual
end
