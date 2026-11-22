import tmp.sheaf.xif.paper.Mzk1Stage4S1902HullConcreteActual

/-! # Mzk1Stage4ComparisonRegionActual (stage4 lane; unique filename)

A614 module: concrete comparison region between a point q-region and the concrete hull,
with strict measured comparison and a concrete bridge to the strict_measure shape.
No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4ComparisonRegionActual

open MeasureTheory
open scoped ENNReal
open LeanFormal.IUT.XiFPaper.Mzk1Stage4S1902HullConcreteActual

/-- The point q-region `{0}`. -/
def qRegionPoint : Set Real := {0}

/-- The point q-region has measure zero. -/
theorem qRegionPoint_measure : volume qRegionPoint = 0 := by
  unfold qRegionPoint
  exact Real.volume_singleton

/-- The measured comparison is strict: `0 < 2`. -/
theorem comparison_strict :
    (volume qRegionPoint).toReal < (volume concreteHull.region).toReal := by
  rw [qRegionPoint_measure, concreteHull_measure]
  norm_num

/-- The annulus (hull minus q-region) still has measure 2 (the point has measure 0). -/
theorem annulus_measure :
    volume (concreteHull.region \ qRegionPoint) = ENNReal.ofReal 2 := by
  have hmeas : MeasurableSet (concreteHull.region \ qRegionPoint) :=
    concreteHull.measurable.diff (by unfold qRegionPoint; exact measurableSet_singleton 0)
  have h1 : volume (concreteHull.region \ qRegionPoint) ≤ volume concreteHull.region :=
    measure_mono Set.diff_subset
  have hsub : concreteHull.region ⊆
      (concreteHull.region \ qRegionPoint) ∪ qRegionPoint := by
    intro x hx
    by_cases hq : x ∈ qRegionPoint
    · exact Or.inr hq
    · exact Or.inl ⟨hx, hq⟩
  have h2 : volume concreteHull.region ≤ volume (concreteHull.region \ qRegionPoint) :=
    by
    have h3 : volume concreteHull.region ≤ volume ((concreteHull.region \ qRegionPoint) ∪ qRegionPoint) :=
      measure_mono hsub
    have h4 : volume ((concreteHull.region \ qRegionPoint) ∪ qRegionPoint) ≤ volume (concreteHull.region \ qRegionPoint) + volume qRegionPoint :=
      measure_union_le _ _
    rw [qRegionPoint_measure, add_zero] at h4
    exact le_trans h3 h4
  have heq : volume (concreteHull.region \ qRegionPoint) = volume concreteHull.region :=
    le_antisymm h1 h2
  rw [heq, concreteHull_measure]
/-- Concrete bridge: the strict_measure comparison for the concrete regions. -/
structure ConcreteBridge where
  /-- the q-region. -/
  qRegion : Set Real
  /-- the hull region. -/
  hullRegion : Set Real
  /-- q-region lies in the hull. -/
  subset : qRegion ⊆ hullRegion
  /-- the measured strict comparison. -/
  strict : (volume qRegion).toReal < (volume hullRegion).toReal

/-- The concrete bridge instance for `{0} ⊂ [-1,1]`. -/
noncomputable def concreteBridge : ConcreteBridge where
  qRegion := qRegionPoint
  hullRegion := concreteHull.region
  subset := by
    intro x hx
    unfold qRegionPoint at hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  strict := comparison_strict

/-- Consumer: the concrete bridge gives the strict measured comparison. -/
theorem concreteBridge_strict :
    (volume concreteBridge.qRegion).toReal <
      (volume concreteBridge.hullRegion).toReal :=
  concreteBridge.strict

#check qRegionPoint
#check comparison_strict
#check annulus_measure
#check ConcreteBridge
#check concreteBridge
#check concreteBridge_strict

end LeanFormal.IUT.XiFPaper.Mzk1Stage4ComparisonRegionActual
end
