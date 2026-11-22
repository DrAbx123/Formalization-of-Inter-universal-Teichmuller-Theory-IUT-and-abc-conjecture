import tmp.sheaf.xif.paper.Mzk1S1DisplayCThetaActualV2

/-! Mainline: CTheta paper bound -> hCor312 / Thm 1.10 display (re-export consumers). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1CThetaToHCor312Actual

open LeanFormal.IUT.XiFPaper.Mzk1S1DisplayCThetaActualV2

theorem cTheta_to_hCor312 (T : LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual.Thm110DisplayTerms)
    (l : PrimeGeFive) (dFpd fFpd : Real)
    (hL : T.l = (l.value : Real))
    (hD : T.logDFpd = Real.log dFpd) (hF : T.logFFpd = Real.log fFpd)
    (hlogQ : 0 < T.logQ)
    (hC : -1 ≤ LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual.CThetaPaper
      l T.logQ T.dmod dFpd fFpd T.eStar T.etaPrm) :
    LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual.thm110Lhs T ≤
      LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual.thm110Mid T +
        LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual.thm110Cor312Gap T :=
  LeanFormal.IUT.XiFPaper.Mzk1S1DisplayCThetaActualV2.hCor312_of_CThetaPaper_ge_neg_one
    T l dFpd fFpd hL hD hF hlogQ hC

theorem cTheta_to_display
    (T : LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual.Thm110DisplayTerms)
    (l : PrimeGeFive) (dFpd fFpd : Real)
    (hL : T.l = (l.value : Real))
    (hD : T.logDFpd = Real.log dFpd) (hF : T.logFFpd = Real.log fFpd)
    (hlogQ : 0 < T.logQ)
    (hC : -1 ≤ LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual.CThetaPaper
      l T.logQ T.dmod dFpd fFpd T.eStar T.etaPrm)
    (hl : 0 < T.l) (hd : 0 ≤ T.dmod)
    (hsum : 0 ≤ T.logDFpd + T.logFFpd)
    (he : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hQ : T.logQ ≤ (4 * T.dmod * T.l) * (T.logDFpd + T.logFFpd) +
      5 * T.l ^ 2 * (T.eStar * T.l + T.etaPrm)) :
    LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual.thm110Lhs T ≤
      LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual.thm110Rhs T :=
  LeanFormal.IUT.XiFPaper.Mzk1S1DisplayCThetaActualV2.thm110_final_display_of_CThetaPaper_logQ
    T l dFpd fFpd hL hD hF hlogQ hC hl hd hsum he hQ

end LeanFormal.IUT.XiFPaper.Mzk1CThetaToHCor312Actual