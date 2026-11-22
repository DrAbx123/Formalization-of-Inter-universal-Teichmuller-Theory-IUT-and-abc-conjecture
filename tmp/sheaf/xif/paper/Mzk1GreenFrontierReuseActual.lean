import tmp.sheaf.xif.paper.Mzk1S1DisplayFActual
import tmp.sheaf.xif.paper.Mzk1G2FrontierActual
import tmp.sheaf.xif.paper.Mzk1E5RegionConsumerActual

/-! Mainline: reuse-chain re-exports from green display-F / frontier / E5-region assets. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GreenFrontierReuseActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual

universe u

theorem thm110_final_display_F_bound_reuse (T : Thm110DisplayTerms)
    (H : Thm110DisplayInputs T) (logDF logFF : Real)
    (hcoef : 0 ≤ 1 + 20 * T.dmod / T.l)
    (hsumle : T.logDFpd + T.logFFpd ≤ logDF + logFF) :
    thm110Lhs T ≤ (1 + 20 * T.dmod / T.l) * (logDF + logFF) +
      20 * (T.eStar * T.l + T.etaPrm) :=
  LeanFormal.IUT.XiFPaper.Mzk1S1DisplayFActual.thm110_final_display_F_bound
    T H logDF logFF hcoef hsumle

theorem abcConjecture_of_frontierRoute_reuse (h : ABCFrontier.{u}) : ABCConjecture :=
  LeanFormal.IUT.XiFPaper.Mzk1G2FrontierActual.abcConjecture_of_frontierRoute h

theorem regionVolumeFamily_of_undilatedBound_reuse {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (h : UndilatedRegionBound W pt) : RegionVolumeFamily W pt :=
  LeanFormal.IUT.XiFPaper.Mzk1E5RegionConsumerActual.regionVolumeFamily_of_undilatedBound h

theorem abcConjecture_of_undilatedBounds_reuse {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (hb : UndilatedHeightBound W pt) (hc : UndilatedRegionBound W pt) :
    ABCConjecture :=
  LeanFormal.IUT.XiFPaper.Mzk1E5RegionConsumerActual.abcConjecture_of_undilatedBounds hb hc

theorem s1DisplayFRows_length_reuse :
    LeanFormal.IUT.XiFPaper.Mzk1S1DisplayFActual.s1DisplayFRows.length = 4 :=
  LeanFormal.IUT.XiFPaper.Mzk1S1DisplayFActual.s1DisplayFRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GreenFrontierReuseActual