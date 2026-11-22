import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.MetricSpace.ProperSpace

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# Nonarchimedean unit-sphere Haar mass

The nonarchimedean norm-one sphere is open (ultrametric argument), compact
(closed subset of the compact unit ball), and nonempty.  Hence its additive
Haar measure is positive and finite.  This is the actual mass statement needed
for the finite-place Adm reference/region.

No archimedean claim is made here; the archimedean sphere is a separate
zero-mass branch.
-/

noncomputable section

open MeasureTheory Set Metric

namespace LeanFormal.IUT.N8Closure.P6NonarchSphereMassActual

universe u

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K]

/-- The actual norm-one unit sphere. -/
def unitSphere (K : Type u) [NormedField K] : Set K :=
  {x | ‖x‖ = 1}

/-- In an ultrametric field the norm-one sphere is open: a ball of radius
one around any point of the sphere stays in the sphere. -/
theorem isOpen_unitSphere : IsOpen (unitSphere K) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx1 : ‖x‖ = 1 := hx
  filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with y hy
  have hdist : ‖y - x‖ < 1 := by simpa [dist_eq_norm] using hy
  have hxsub : ‖x - y‖ < 1 := by simpa [norm_sub_rev, dist_eq_norm] using hy
  have hupper : ‖y‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max x (y - x)
    have hmax : max ‖x‖ ‖y - x‖ = 1 := by rw [hx1]; exact max_eq_left hdist.le
    calc
      ‖y‖ = ‖x + (y - x)‖ := by ring_nf
      _ ≤ max ‖x‖ ‖y - x‖ := h
      _ = 1 := hmax
  have hlower : (1 : ℝ) ≤ ‖y‖ := by
    have h := IsUltrametricDist.norm_add_le_max y (x - y)
    have hxle : ‖x‖ ≤ max ‖y‖ ‖x - y‖ := by
      calc
        ‖x‖ = ‖y + (x - y)‖ := by ring_nf
        _ ≤ max ‖y‖ ‖x - y‖ := h
    have hmax : (1 : ℝ) ≤ max ‖y‖ ‖x - y‖ := by
      rw [← hx1]
      exact hxle
    by_contra hnot
    have hylt : ‖y‖ < 1 := lt_of_not_ge hnot
    have hmaxlt : max ‖y‖ ‖x - y‖ < 1 := max_lt hylt hxsub
    linarith
  have hy1 : ‖y‖ = 1 := le_antisymm hupper hlower
  exact hy1

theorem isCompact_unitSphere : IsCompact (unitSphere K) := by
  have hsub : unitSphere K ⊆ Metric.closedBall (0 : K) 1 := by
    intro x hx
    have hx1 : ‖x‖ = 1 := hx
    simpa [dist_eq_norm, hx1]
  have hclosed : IsClosed (unitSphere K) := by
    simpa [unitSphere] using isClosed_eq continuous_norm continuous_const
  exact (isCompact_closedBall (0 : K) 1).of_isClosed_subset hclosed hsub

/-- The nonarchimedean unit sphere has positive and finite additive Haar mass. -/
theorem unitSphere_measure_pos_lt_top
    (mu : Measure K) [Measure.IsAddHaarMeasure mu] :
    0 < mu (unitSphere K) ∧ mu (unitSphere K) < ⊤ := by
  constructor
  · apply Measure.measure_pos_of_nonempty_interior
    refine ⟨(1 : K), ?_⟩
    rw [isOpen_unitSphere.interior_eq]
    simp [unitSphere]
  · exact (isCompact_unitSphere (K := K)).measure_lt_top

end LeanFormal.IUT.N8Closure.P6NonarchSphereMassActual

end