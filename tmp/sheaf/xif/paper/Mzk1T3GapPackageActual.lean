import tmp.sheaf.xif.paper.Mzk1T2ComparisonGapStatementActual
import tmp.sheaf.xif.paper.Mzk1T3FrontierFromComparisonActual

/-!
  Mainline: package form of the two named T2 comparison gaps into the T3 frontier
  clauses and ABC.  Real compositions; the two gap Props remain unproved paper links.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1T3GapPackageActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1T2ComparisonGapStatementActual

universe u

theorem frontierHeightClause_of_heightRegionGap {X : Type u}
    (W : IQHullLogVolumeInterface X)
    (point : ∀ (ε : Real), 0 < ε → Nat → Nat → Nat → X)
    (h : ∀ (ε : Real) (hε : 0 < ε), HeightRegionGap W ε (point ε hε)) :
    FrontierHeightComparisonClause W point :=
  fun ε hε a b c habc => h ε hε a b c habc

theorem frontierRegionClause_of_regionWeightGap {X : Type u}
    (W : IQHullLogVolumeInterface X)
    (point : ∀ (ε : Real), 0 < ε → Nat → Nat → Nat → X)
    (h : ∀ (ε : Real) (hε : 0 < ε), RegionWeightGap W ε (point ε hε)) :
    FrontierRegionComparisonClause W point :=
  fun ε hε => h ε hε

/-- The two-gap package (same point family) is sufficient for ABC via the frontier. -/
theorem abcConjecture_of_gapPackage {X : Type u}
    (W : IQHullLogVolumeInterface X)
    (point : ∀ (ε : Real), 0 < ε → Nat → Nat → Nat → X)
    (hH : ∀ (ε : Real) (hε : 0 < ε), HeightRegionGap W ε (point ε hε))
    (hR : ∀ (ε : Real) (hε : 0 < ε), RegionWeightGap W ε (point ε hε)) :
    ABCConjecture :=
  abcConjecture_of_frontier
    ⟨X, W, point,
     frontierHeightClause_of_heightRegionGap W point hH,
     frontierRegionClause_of_regionWeightGap W point hR⟩

/-- A per-epsilon comparison family gives an existential gap package. -/
theorem gapPackage_of_comparisonFamily {X : Type u}
    (W : IQHullLogVolumeInterface X)
    (C : ∀ (ε : Real) (hε : 0 < ε),
      Cor312EpsilonArithmeticComparison W ε) :
    ∃ point : ∀ (ε : Real), 0 < ε → Nat → Nat → Nat → X,
      (∀ (ε : Real) (hε : 0 < ε), HeightRegionGap W ε (point ε hε)) ∧
        (∀ (ε : Real) (hε : 0 < ε), RegionWeightGap W ε (point ε hε)) :=
  ⟨fun ε hε => (C ε hε).logShellPoint,
   ⟨fun ε hε => (C ε hε).height_le_normalizedRegionVolume,
    fun ε hε => (C ε hε).regionVolume_le_normalizedWeight⟩⟩

/-- Pointwise gap existence (each epsilon may use its own point) implies ABC. -/
theorem abcConjecture_of_gapExistence {X : Type u}
    (W : IQHullLogVolumeInterface X)
    (h : ∀ (ε : Real) (hε : 0 < ε),
      ∃ p : Nat → Nat → Nat → X,
        HeightRegionGap W ε p ∧ RegionWeightGap W ε p) :
    ABCConjecture := by
  have hfamily : ∀ (ε : Real) (hε : 0 < ε),
      Nonempty (Cor312EpsilonArithmeticComparison W ε) := by
    intro ε hε
    exact (t2_gap_statement_iff W ε).mpr (h ε hε)
  refine abcConjecture_of_frontier ⟨X, W,
    (fun ε hε => (Classical.choice (hfamily ε hε)).logShellPoint), ?_, ?_⟩
  · intro ε hε a b c habc
    exact (Classical.choice (hfamily ε hε)).height_le_normalizedRegionVolume a b c habc
  · intro ε hε
    exact (Classical.choice (hfamily ε hε)).regionVolume_le_normalizedWeight

end LeanFormal.IUT.XiFPaper.Mzk1T3GapPackageActual