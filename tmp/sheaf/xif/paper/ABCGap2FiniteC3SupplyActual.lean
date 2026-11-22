import tmp.sheaf.xif.paper.S3128C3RegionVolumeSplitBoundActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction

noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3128C3RegionVolumeSplitBoundActual

namespace LeanFormal.IUT.XiFPaper.ABCGap2FiniteC3SupplyActual

universe u

/-- Explicit intermediate supply for the split form of
`regionVolume_le_normalizedWeight`: the `hunit` and `hpoint` data together
with the split/subadditivity and point-finiteness inputs. This is a DETOUR:
it does not close the named gap-2 paper link, it only records the exact
intermediate input shape and feeds it to the actual
`cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound`. -/
structure ABCGap2FiniteC3Supply {X : Type u} (W : IQHullLogVolumeInterface X)
    (point : Nat → Nat → Nat → X) (eps D₀ D₁ : ℝ) where
  hD₀ : 0 ≤ D₀
  hunit : W.logVolume W.unitRegion ≤ W.logVolume W.hull + ENNReal.ofReal D₀
  hsplit : ∀ a b c : Nat, IsABCTriple a b c →
    W.logVolume (normalizedComparisonRegion W point a b c) ≤
      W.logVolume (W.scaleShift '' W.unitRegion) +
        W.logVolume {W.scaleShift (point a b c)}
  hptfin : ∀ a b c : Nat, IsABCTriple a b c →
    W.logVolume {W.scaleShift (point a b c)} < ⊤
  hpoint : ∀ a b c : Nat, IsABCTriple a b c →
    (W.logVolume {W.scaleShift (point a b c)}).toReal ≤
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D₁

/-- The intermediate supply yields the exact gap-2 field shape with `D = D₀ + D₁`. -/
theorem ABCGap2FiniteC3Supply.regionVolumeBound
    {X : Type u} {W : IQHullLogVolumeInterface X} {point : Nat → Nat → Nat → X}
    {eps D₀ D₁ : ℝ} (S : ABCGap2FiniteC3Supply W point eps D₀ D₁) :
    ∃ D : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (normalizedComparisonRegion W point a b c)).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D :=
  cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound
    W point S.hD₀ S.hunit S.hsplit S.hptfin S.hpoint

/-- Reconciliation with the C3 actual detour: the C3 concrete carrier bound is
exactly a `regionVolume_le_normalizedWeight`-shaped result at constant point `0`. -/
theorem ABCGap2FiniteC3Supply.c3ActualBound
    {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
    [DecidableEq C3.tensorIndex]
    {eps : ℝ} (heps : 0 < eps) :
    ∃ D : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
      ((S3128C3HullInterface (l := l) (V := V) (I := I) C3).logVolume
        (normalizedComparisonRegion (S3128C3HullInterface (l := l) (V := V) (I := I) C3)
          (fun _ _ _ => 0) a b c)).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          ((S3128C3HullInterface (l := l) (V := V) (I := I) C3).logVolume
            (S3128C3HullInterface (l := l) (V := V) (I := I) C3).hull).toReal + D :=
  S3128C3RegionVolume_le_weight_split (l := l) (V := V) (I := I) C3 heps

#check ABCGap2FiniteC3Supply
#check ABCGap2FiniteC3Supply.regionVolumeBound
#check ABCGap2FiniteC3Supply.c3ActualBound

end LeanFormal.IUT.XiFPaper.ABCGap2FiniteC3SupplyActual
end