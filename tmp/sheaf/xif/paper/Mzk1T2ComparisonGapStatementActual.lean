import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
  Mainline: T2 decomposition statement for the two remaining named comparison gaps of
  `Cor312ToABCBridgeInterface` (IUT IV section 2 paper links).

  Statement-shape only: the two Props below are exactly the two unproved paper
  links (height_le_normalizedRegionVolume, regionVolume_le_normalizedWeight).
  No proof of them is produced here and no fake closure is introduced.
  What IS proved: (a) the bundled interface is equivalent to the named point
  together with the two gap Props (structural unpacking), and (b) the derived
  region-finiteness re-export.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1T2ComparisonGapStatementActual

open LeanFormal.IUT

universe u

/-- Gap 1 (IUT IV section 2, height-vs-log-volume comparison), paper link, not proved. -/
def HeightRegionGap {X : Type u} (W : IQHullLogVolumeInterface X) (epsilon : Real)
    (logShellPoint : Nat → Nat → Nat → X) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + epsilon) *
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal

/-- Gap 2 (IUT IV section 2, log-volume computation/estimate), paper link, not proved. -/
def RegionWeightGap {X : Type u} (W : IQHullLogVolumeInterface X) (epsilon : Real)
    (logShellPoint : Nat → Nat → Nat → X) : Prop :=
  ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
    (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal ≤
      (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
        (W.logVolume W.hull).toReal + D

/-- The interface is exactly the named point plus the two gap Props (structural). -/
theorem t2_gap_statement_iff {X : Type u} (W : IQHullLogVolumeInterface X)
    (epsilon : Real) :
    Nonempty (Cor312EpsilonArithmeticComparison W epsilon) ↔
      ∃ p : Nat → Nat → Nat → X,
        HeightRegionGap W epsilon p ∧ RegionWeightGap W epsilon p := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.logShellPoint, C.height_le_normalizedRegionVolume,
      C.regionVolume_le_normalizedWeight⟩
  · rintro ⟨p, h1, h2⟩
    exact ⟨{ logShellPoint := p
             height_le_normalizedRegionVolume := h1
             regionVolume_le_normalizedWeight := h2 }⟩

/-- Re-export: the region log-volume is finite on ABC triples (derived, no gap). -/
theorem t2_region_logVolume_lt_top {X : Type u} {W : IQHullLogVolumeInterface X}
    {epsilon : Real} (C : Cor312EpsilonArithmeticComparison W epsilon) :
    ∀ a b c : Nat, IsABCTriple a b c →
      W.logVolume (C.comparisonRegion a b c) < ⊤ :=
  Cor312EpsilonArithmeticComparison.comparisonRegion_logVolume_lt_top C

end LeanFormal.IUT.XiFPaper.Mzk1T2ComparisonGapStatementActual