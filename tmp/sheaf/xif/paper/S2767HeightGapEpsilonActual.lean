import tmp.sheaf.xif.paper.S2766EpsilonComparisonGapActual

noncomputable section
open scoped ENNReal nonZeroDivisors Classical Pointwise
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2767HeightGapEpsilonActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2766EpsilonComparisonGapActual
open LeanFormal.IUT.XiFPaper.S2758MixedSpaceIQHullActual
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open LeanFormal.IUT.XiFPaper.S2760MixedSpacePaperFactorActual
open LeanFormal.IUT.XiFPaper.S2765PointMapActual

universe u

variable (K : Type u) [Field K] [NumberField K]
variable (J : (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ)

/-- The S2766 comparison region is the S2760 hull together with the scaled
candidate point. -/
theorem S2767_region_eq_hull_union (eps : Real) (a n c : Nat) :
    S2766ComparisonRegion K J eps a n c =
      (S2760IQHullInterface K J).hull ∪
        {S2760R K J • S2766LogShellPoint K a n c} := by
  unfold S2766ComparisonRegion normalizedComparisonRegion
  rw [Set.image_union]
  change (fun x => S2760R K J • x) '' S2758UnitRegion K ∪
      (fun x => S2760R K J • x) '' {S2766LogShellPoint K a n c} =
    (S2760R K J • S2758UnitRegion K) ∪
      {S2760R K J • S2766LogShellPoint K a n c}
  rw [← Set.image_smul]
  simp

theorem S2767_region_volume_eq_hull (eps : Real) (a n c : Nat) :
    volume (S2766ComparisonRegion K J eps a n c) =
      volume (S2760IQHullInterface K J).hull := by
  rw [S2767_region_eq_hull_union]
  apply le_antisymm
  · calc volume ((S2760IQHullInterface K J).hull ∪
        {S2760R K J • S2766LogShellPoint K a n c})
        ≤ volume (S2760IQHullInterface K J).hull +
          volume ({S2760R K J • S2766LogShellPoint K a n c} :
            Set (NumberField.mixedEmbedding.mixedSpace K)) :=
        measure_union_le _ _
      _ = volume (S2760IQHullInterface K J).hull := by
        rw [NullSingletonClass.measure_singleton]
        exact add_zero _
  · exact measure_mono (Set.subset_union_left)

theorem S2767_region_logVolume_eq_hull (eps : Real) (a n c : Nat) :
    (S2760IQHullInterface K J).logVolume
        (S2766ComparisonRegion K J eps a n c) =
      (S2760IQHullInterface K J).logVolume
        (S2760IQHullInterface K J).hull := by
  change haarLogVolume volume (S2766ComparisonRegion K J eps a n c) =
    haarLogVolume volume (S2760IQHullInterface K J).hull
  unfold haarLogVolume
  rw [S2767_region_volume_eq_hull]

/-- The log-volume side of the epsilon comparison is actual for the candidate
region, as soon as `0 ≤ 1 + eps`: the region differs from the hull by a null
singleton and `D = 0` works. -/
theorem S2767_regionVolume_le_normalizedWeight (eps : Real)
    (hε : 0 ≤ 1 + eps) :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      ((S2760IQHullInterface K J).logVolume
        (S2766ComparisonRegion K J eps a b c)).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          ((S2760IQHullInterface K J).logVolume
            (S2760IQHullInterface K J).hull).toReal + D := by
  refine ⟨0, fun a b c _ => ?_⟩
  rw [S2767_region_logVolume_eq_hull]
  have hw : 0 ≤ arithmeticWeight (abcRationalPoint a c) :=
    arithmeticWeight_nonneg _
  have hmul : 0 ≤ (1 + eps) * arithmeticWeight (abcRationalPoint a c) :=
    mul_nonneg hε hw
  linarith

/-- Height gap only: the sole remaining paper inequality for the candidate point
map. -/
structure S2767HeightGapOnly (eps : Real) where
  hε : 0 ≤ 1 + eps
  height_le_region :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) *
          ((S2760IQHullInterface K J).logVolume
            (S2766ComparisonRegion K J eps a b c)).toReal

/-- From the explicit height gap only, build the actual epsilon comparison:
the log-volume side is proved, not assumed. -/
noncomputable def S2767EpsilonComparisonOfHeightGap (eps : Real)
    (H : S2767HeightGapOnly K J eps) :
    Cor312EpsilonArithmeticComparison (S2760IQHullInterface K J) eps where
  logShellPoint := S2766LogShellPoint K
  height_le_normalizedRegionVolume := H.height_le_region
  regionVolume_le_normalizedWeight :=
    S2767_regionVolume_le_normalizedWeight K J eps H.hε

#check S2767_region_eq_hull_union
#check S2767_region_volume_eq_hull
#check S2767_region_logVolume_eq_hull
#check S2767_regionVolume_le_normalizedWeight
#check S2767HeightGapOnly
#check S2767EpsilonComparisonOfHeightGap
#print axioms S2767EpsilonComparisonOfHeightGap

end LeanFormal.IUT.XiFPaper.S2767HeightGapEpsilonActual
end
