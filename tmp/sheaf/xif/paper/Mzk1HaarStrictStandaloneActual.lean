/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual

/-!
# A557 standalone annulus measure: half-ball q-region vs the actual hull

Self-contained (green dependencies only) positive-measure half-ball region and the
strict-measure reduction to the ANNULUS positive measure:

* `halfBallRegion T = pi_b closedBall 0 (R_b/2)` is contained in the actual hull
  `s1902Hull T` and has PROVED positive and finite product Haar measure;
* the hull is the disjoint union of the half-ball and the open annulus
  `annulus T = s1902Hull T \ halfBallRegion T`; if the annulus has positive measure
  (the remaining annulus step), then the hull has strictly larger Haar measure:
  `strict_measure_of_annulus`.

This isolates the annulus positivity as the last geometric input, with all other
measure facts proved.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HaarStrictStandaloneActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The half-ball q-region: product of closed balls of half the hull radius. -/
def halfBallRegion : Set (S1902Carrier T) :=
  Set.pi Set.univ (fun b =>
    Metric.closedBall (0 : rootNormedExtension T b)
      ((rootImageRadius T b : Real) / 2))

/-- The half-ball q-region is contained in the actual hull. -/
theorem halfBallRegion_subset_hull : halfBallRegion T ⊆ s1902Hull T := by
  intro x hx
  rw [s1902Hull, rootExtensionProductImageHull]
  intro b _
  have hxb := hx b (Set.mem_univ b)
  rw [Metric.mem_closedBall] at hxb ⊢
  rw [dist_zero_right] at hxb ⊢
  have hnonneg : (0 : Real) ≤ (rootImageRadius T b : Real) := NNReal.coe_nonneg _
  linarith

/-- The half-ball q-region has positive product Haar measure. -/
theorem halfBallRegion_measure_pos :
    0 < rootExtensionProductHaar T (halfBallRegion T) := by
  unfold halfBallRegion rootExtensionProductHaar
  rw [Measure.pi_pi]
  rw [pos_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr (fun b _ => by
    have hr : (0 : Real) < (rootImageRadius T b : Real) / 2 := by
      have hpos : (0 : Real) < (rootImageRadius T b : Real) :=
        NNReal.coe_pos.mpr (rootImageRadius_pos (T := T) (b := b))
      linarith
    exact ne_of_gt (rootExtensionClosedBall_measure_pos (T := T) (b := b) _ hr))

/-- The half-ball q-region has finite product Haar measure. -/
theorem halfBallRegion_measure_lt_top :
    rootExtensionProductHaar T (halfBallRegion T) < ⊤ := by
  unfold halfBallRegion rootExtensionProductHaar
  rw [Measure.pi_pi]
  apply ENNReal.prod_lt_top
  intro b _
  exact rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _

/-- The annulus: hull minus the half-ball. -/
def annulus : Set (S1902Carrier T) :=
  s1902Hull T \ halfBallRegion T

/-- The half-ball region is measurable (finite product of closed balls). -/
theorem halfBallRegion_measurable : MeasurableSet (halfBallRegion T) := by
  unfold halfBallRegion
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_closedBall)

/-- The annulus is measurable. -/
theorem annulus_measurable : MeasurableSet (annulus T) := by
  unfold annulus
  exact (s1902Hull_compact T).measurableSet.diff (halfBallRegion_measurable T)

/-- The half-ball and the annulus are disjoint. -/
theorem halfBall_disjoint_annulus : Disjoint (halfBallRegion T) (annulus T) :=
  Set.disjoint_left.mpr (fun _ hx hxa => hxa.2 hx)

/-- The hull is the union of the half-ball and the annulus. -/
theorem hull_eq_halfBall_union_annulus :
    s1902Hull T = halfBallRegion T ∪ annulus T := by
  ext x
  constructor
  · intro hx
    by_cases hxin : x ∈ halfBallRegion T
    · exact Or.inl hxin
    · exact Or.inr ⟨hx, hxin⟩
  · rintro (h | ⟨h, _⟩)
    · exact halfBallRegion_subset_hull T h
    · exact h

/-- **Strict measure from the annulus**: if the annulus has positive Haar measure,
  the hull has strictly larger Haar measure than the half-ball. -/
theorem strict_measure_of_annulus (hann : 0 < rootExtensionProductHaar T (annulus T)) :
    rootExtensionProductHaar T (halfBallRegion T) <
      rootExtensionProductHaar T (s1902Hull T) := by
  have hfin : rootExtensionProductHaar T (halfBallRegion T) < ⊤ :=
    halfBallRegion_measure_lt_top T
  rw [hull_eq_halfBall_union_annulus T,
    measure_union (halfBall_disjoint_annulus T) (annulus_measurable T)]
  exact ENNReal.lt_add_right (ne_of_lt hfin) (ne_of_gt hann)

end Mzk1HaarStrictStandaloneActual

end
-- A559: force recompile after stale-log race.
