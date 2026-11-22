import tmp.sheaf.xif.paper.Mzk1S1DisplayCThetaActualV2
import tmp.sheaf.xif.paper.Mzk1S1DisplayFActual
import tmp.sheaf.xif.paper.Mzk1G2EGapInputsActual
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

/-! Mainline: chain consumers combining Thm 1.10 display conclusions with ABC conclusions
  from independent hypothesis families (new conjunctions, no re-export only). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DisplayABCChainActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1S1DisplayCThetaActualV2
open LeanFormal.IUT.XiFPaper.Mzk1S1DisplayFActual
open LeanFormal.IUT.XiFPaper.Mzk1G2EGapInputsActual

universe u

/-- Display (from CTheta bound + logQ bound) together with ABC (from G2.e gap inputs). -/
theorem display_and_abc_of_cTheta_gapInputs (T : Thm110DisplayTerms)
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
      5 * T.l ^ 2 * (T.eStar * T.l + T.etaPrm))
    {X : Type u} {W : IQHullLogVolumeInterface X}
    (logShellPoint : Nat → Nat → Nat → X)
    (I : ∀ epsilon : Real, 0 < epsilon → EpsilonGapInputs W logShellPoint epsilon) :
    thm110Lhs T ≤ thm110Rhs T ∧ ABCConjecture :=
  ⟨thm110_final_display_of_CThetaPaper_logQ T l dFpd fFpd hL hD hF hlogQ hC
      hl hd hsum he hQ,
   abcConjecture_of_gapInputs X W logShellPoint I⟩

/-- Display F-bound together with ABC from the additive V2 contract. -/
theorem displayF_and_abc_of_additiveV2 (T : Thm110DisplayTerms)
    (H : Thm110DisplayInputs T) (logDF logFF : Real)
    (hcoef : 0 ≤ 1 + 20 * T.dmod / T.l)
    (hsumle : T.logDFpd + T.logFFpd ≤ logDF + logFF)
    (hV2 : ABCHeightWeightAdditiveBoundV2) :
    thm110Lhs T ≤ (1 + 20 * T.dmod / T.l) * (logDF + logFF) +
      20 * (T.eStar * T.l + T.etaPrm) ∧ ABCConjecture :=
  ⟨thm110_final_display_F_bound T H logDF logFF hcoef hsumle,
   abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mpr hV2⟩

end LeanFormal.IUT.XiFPaper.Mzk1DisplayABCChainActual