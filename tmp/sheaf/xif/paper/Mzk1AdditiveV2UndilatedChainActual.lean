import tmp.sheaf.xif.paper.Mzk1E5AdditiveHeightActualV2
import LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual
import LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
import LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual

/-! Mainline: chain consumer from additive V2 + volume dominance + (c) region bound
  to the undilated height bound and ABC (new composition, no re-export only). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1AdditiveV2UndilatedChainActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1E5AdditiveHeightActualV2
open LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual

universe u

theorem undilatedHeight_and_region_imp_abc {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (hV2 : ABCHeightWeightAdditiveBoundV2) {A : Real}
    (hA : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        2 * arithmeticWeight (abcRationalPoint a c) + A)
    (hvol : ∀ a b c : Nat, IsABCTriple a b c →
      2 * arithmeticWeight (abcRationalPoint a c) + A ≤
        (W.logVolume {pt a b c}).toReal)
    (hc : UndilatedRegionBound W pt) :
    UndilatedHeightBound W pt ∧ ABCConjecture :=
  ⟨undilatedHeightBound_of_additiveBound_volume hV2 hA hvol,
   abcConjecture_of_undilated
     (undilatedHeightBound_of_additiveBound_volume hV2 hA hvol) hc⟩

end LeanFormal.IUT.XiFPaper.Mzk1AdditiveV2UndilatedChainActual