import tmp.sheaf.xif.paper.Mzk1E5DisplaySlackActualV2
import tmp.sheaf.xif.paper.Mzk1G3BridgesActualV2
import tmp.sheaf.xif.paper.Mzk1Cor312ObligationConsumerActual

/-! Mainline: reuse-chain re-exports from green E5/G3/obligation assets. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GreenChainReuseActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual

universe u

theorem e5_display_slack_reuse (T : Thm110DisplayTerms)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T)
    (hl : 0 < T.l) (hd : 0 ≤ T.dmod)
    (hsum : 0 ≤ T.logDFpd + T.logFFpd)
    (he : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hQ : T.logQ ≤ (4 * T.dmod * T.l) * (T.logDFpd + T.logFFpd) +
      5 * T.l ^ 2 * (T.eStar * T.l + T.etaPrm)) :
    thm110Lhs T ≤ thm110Rhs T :=
  LeanFormal.IUT.XiFPaper.Mzk1E5DisplaySlackActualV2.thm110_final_display_of_logQ_slack
    T hCor312 hl hd hsum he hQ

theorem e5_display_and_abc_reuse {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (T : Thm110DisplayTerms)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T)
    (hl : 0 < T.l) (hd : 0 ≤ T.dmod)
    (hsum : 0 ≤ T.logDFpd + T.logFFpd)
    (he : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hQ : T.logQ ≤ (4 * T.dmod * T.l) * (T.logDFpd + T.logFFpd) +
      5 * T.l ^ 2 * (T.eStar * T.l + T.etaPrm))
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    thm110Lhs T ≤ thm110Rhs T ∧ ABCConjecture :=
  LeanFormal.IUT.XiFPaper.Mzk1E5DisplaySlackActualV2.thm110_display_and_abc_of_logQ_bound
    T hCor312 hl hd hsum he hQ hb hc

theorem g3_bridges_rows_reuse :
    LeanFormal.IUT.XiFPaper.Mzk1G3BridgesActualV2.g3BridgesRows.length = 5 :=
  LeanFormal.IUT.XiFPaper.Mzk1G3BridgesActualV2.g3BridgesRows_length

theorem obligation_ids_reuse :
    LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual.ipl.id = "IUT-III.IPL" ∧
      LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual.she.id = "IUT-III.SHE" ∧
      LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual.apt.id = "IUT-III.APT" :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual.ipl_id,
   LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual.she_id,
   LeanFormal.IUT.XiFPaper.Mzk1Cor312ObligationConsumerActual.apt_id⟩

end LeanFormal.IUT.XiFPaper.Mzk1GreenChainReuseActual