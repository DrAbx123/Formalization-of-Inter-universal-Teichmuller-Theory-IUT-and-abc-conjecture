import tmp.sheaf.xif.paper.Mzk1E5AdditiveHeightActualV2
import tmp.sheaf.xif.paper.Mzk1G3PointwiseWeakenedActualV2
import tmp.sheaf.xif.paper.Mzk1E5S2717ConsumerActualV2

/-! Mainline: reuse-chain re-exports from green additive/G3/S2717 V2 assets. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GreenV2ReuseActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3131PaperRouteHeightReductionActual
open LeanFormal.IUT.XiFPaper.S3131PaperRouteRegionReductionActual

universe u

theorem exists_additive_constant_reuse (h : ABCHeightWeightAdditiveBoundV2) :
    ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        2 * arithmeticWeight (abcRationalPoint a c) + A :=
  LeanFormal.IUT.XiFPaper.Mzk1E5AdditiveHeightActualV2.exists_additive_constant h

theorem undilatedHeightBound_of_additiveBound_volume_reuse {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (h : ABCHeightWeightAdditiveBoundV2) {A : Real}
    (hA : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        2 * arithmeticWeight (abcRationalPoint a c) + A)
    (hvol : ∀ a b c : Nat, IsABCTriple a b c →
      2 * arithmeticWeight (abcRationalPoint a c) + A ≤
        (W.logVolume {pt a b c}).toReal) :
    UndilatedHeightBound W pt :=
  LeanFormal.IUT.XiFPaper.Mzk1E5AdditiveHeightActualV2.undilatedHeightBound_of_additiveBound_volume
    h hA hvol

theorem gapReduced_of_pointwiseWeakened_reuse
    (h : ABCFrontierPointwiseWeakened.{u}) : ABCFrontierGapReduced.{u} :=
  LeanFormal.IUT.XiFPaper.Mzk1G3PointwiseWeakenedActualV2.gapReduced_of_pointwiseWeakened h

theorem abcConjecture_of_pointwiseWeakened_via_gap_reuse
    (h : ABCFrontierPointwiseWeakened.{u}) : ABCConjecture :=
  LeanFormal.IUT.XiFPaper.Mzk1G3PointwiseWeakenedActualV2.abcConjecture_of_pointwiseWeakened_via_gap h

theorem pointwiseReduced_empty_reuse :
    ¬ ABCFrontierPointwiseReduced.{u} :=
  LeanFormal.IUT.XiFPaper.Mzk1G3PointwiseWeakenedActualV2.pointwiseReduced_empty

theorem s2717_consumer_rows_length_reuse :
    LeanFormal.IUT.XiFPaper.Mzk1E5S2717ConsumerActualV2.e5S2717RowsV2.length = 3 :=
  LeanFormal.IUT.XiFPaper.Mzk1E5S2717ConsumerActualV2.e5S2717RowsV2_length

end LeanFormal.IUT.XiFPaper.Mzk1GreenV2ReuseActualAdapted