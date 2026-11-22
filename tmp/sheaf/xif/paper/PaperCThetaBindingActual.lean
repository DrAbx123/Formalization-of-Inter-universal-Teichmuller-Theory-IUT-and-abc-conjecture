/- Paper CTheta binding from actual paper parameters. -/
import tmp.sheaf.xif.paper.S2959PaperParamsActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.PaperCThetaBindingActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2959PaperParamsActual
/-- The actual paper CThetaPaper from a paper parameter source. -/
noncomputable def paperCTheta {a b c : Nat} (P : PaperParamSource a b c) : Real :=
  CThetaPaper P.l P.logQ P.dmod P.dFpd P.fFpd P.eStar P.etaPrm
/-- Definitional binding to the six S2959 actual paper parameters. -/
theorem paperCTheta_eq_binding {a b c : Nat} (P : PaperParamSource a b c) :
    paperCTheta P =
      CThetaPaper P.l (S2959LogQAt P) (S2959DmodAt P) (S2959DFpdAt P)
        (S2959FFpdAt P) (S2959EStarAt P) (S2959EtaPrmAt P) := rfl
#check paperCTheta
#check paperCTheta_eq_binding
end LeanFormal.IUT.XiFPaper.PaperCThetaBindingActual
end
