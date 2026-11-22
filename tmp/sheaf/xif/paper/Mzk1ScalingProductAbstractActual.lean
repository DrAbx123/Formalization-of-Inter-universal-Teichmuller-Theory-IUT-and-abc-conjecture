import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! # Mzk1ScalingProductAbstractActual — product closed-ball Haar positivity (abstract)

A563 chain-independent module (no new mathematics): the abstract Haar-positivity lemma
used by the R/p scaling-product chain: a product of positive-radius closed balls on
`Fin n → ℝ` has positive finite volume.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ScalingProductAbstractActual

open MeasureTheory
open scoped ENNReal BigOperators

/-- Volume of a product of positive closed balls in `Fin n → ℝ` is positive. -/
theorem product_closedBall_volume_pos {n : Nat} (r : Fin n → Real)
    (hr : ∀ i, 0 < r i) :
    0 < volume (Set.pi Set.univ
      (fun i : Fin n => Metric.closedBall (0 : Real) (r i))) :=
  by
  change Measure.pi (fun _ : Fin n => (volume : Measure Real))
    (Set.pi Set.univ (fun i : Fin n => Metric.closedBall (0 : Real) (r i))) = _
  rw [Measure.pi_pi]
  · refine Finset.prod_pos (fun i _ => ?_)
    exact Metric.measure_closedBall_pos _ (hr i)
  · intro i _
    exact Metric.isClosed_closedBall.measurableSet

/-- The product closed-ball region has finite volume. -/
theorem product_closedBall_volume_lt_top {n : Nat} (r : Fin n → Real) :
    volume (Set.pi Set.univ
      (fun i : Fin n => Metric.closedBall (0 : Real) (r i))) < ⊤ :=
  by
  change Measure.pi (fun _ : Fin n => (volume : Measure Real))
    (Set.pi Set.univ (fun i : Fin n => Metric.closedBall (0 : Real) (r i))) < ⊤
  rw [Measure.pi_pi]
  · refine ENNReal.prod_lt_top (fun i _ => ?_)
    exact Metric.measure_closedBall_lt_top
  · intro i _
    exact Metric.isClosed_closedBall.measurableSet

#check product_closedBall_volume_pos
#check product_closedBall_volume_lt_top

end LeanFormal.IUT.XiFPaper.Mzk1ScalingProductAbstractActual
end
