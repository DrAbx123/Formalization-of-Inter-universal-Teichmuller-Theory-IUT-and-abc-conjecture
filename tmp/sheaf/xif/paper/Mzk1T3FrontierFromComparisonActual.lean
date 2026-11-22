import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier

/-!
  Mainline: T2 -> T3 composition.  Given a fixed carrier/hull interface and a
  per-epsilon family of the two-gap comparison data, produce the two frontier
  clauses (F4/F5) and hence ABCConjecture through the proved frontier assembly.
  No gap is proved here; this is wiring/composition only.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1T3FrontierFromComparisonActual

open LeanFormal.IUT

universe u

/-- Per-epsilon comparison data yields the frontier height clause F4. -/
theorem frontierHeightClause_of_comparison {X : Type u}
    (W : IQHullLogVolumeInterface X)
    (C : ∀ (ε : Real) (hε : 0 < ε), Cor312EpsilonArithmeticComparison W ε) :
    FrontierHeightComparisonClause W
      (fun ε hε => (C ε hε).logShellPoint) := by
  intro ε hε a b c habc
  exact (C ε hε).height_le_normalizedRegionVolume a b c habc

/-- Per-epsilon comparison data yields the frontier region-volume clause F5. -/
theorem frontierRegionClause_of_comparison {X : Type u}
    (W : IQHullLogVolumeInterface X)
    (C : ∀ (ε : Real) (hε : 0 < ε), Cor312EpsilonArithmeticComparison W ε) :
    FrontierRegionComparisonClause W
      (fun ε hε => (C ε hε).logShellPoint) := by
  intro ε hε
  exact (C ε hε).regionVolume_le_normalizedWeight

/-- The comparison family inhabits the frontier and hence yields ABC. -/
theorem abcConjecture_of_comparisonFamily {X : Type u}
    (W : IQHullLogVolumeInterface X)
    (C : ∀ (ε : Real) (hε : 0 < ε), Cor312EpsilonArithmeticComparison W ε) :
    ABCConjecture :=
  abcConjecture_of_frontier
    ⟨X, W, (fun ε hε => (C ε hε).logShellPoint),
     frontierHeightClause_of_comparison W C,
     frontierRegionClause_of_comparison W C⟩

end LeanFormal.IUT.XiFPaper.Mzk1T3FrontierFromComparisonActual