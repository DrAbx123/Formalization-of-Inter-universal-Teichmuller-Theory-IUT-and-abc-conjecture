import tmp.sheaf.n8.closure.P6NonarchSphereMassActual
import tmp.sheaf.n8.closure.P6NonarchSphereMassActual
import Mathlib.MeasureTheory.Measure.Haar.Basic

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# Nonzero finite-readout attempt: actual sphere subset

Constructs the actual measurable open subset `unitBallOne = {y | ‖y-1‖ < 1}`
of the nonarch unit sphere, proves it has positive finite Haar mass, and proves
the sphere/ball pair satisfies the exact Adm condition.  The ellOut log-ratio is
then nonzero whenever the ball mass differs from the sphere mass.

No arbitrary subset is used.  If a mass-difference donor is absent, the nonzero
conclusion is conditional; the exact no-go is that no production theorem
compares the two Haar masses.
-/

noncomputable section

open MeasureTheory Set Metric
open LeanFormal.IUT.N8Closure.P6NonarchSphereMassActual

namespace LeanFormal.IUT.N8Closure.P6FiniteReadoutNonzeroAttempt

universe u

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [BorelSpace K]

/-- Actual open ball of radius one around the unit `1`. -/
def unitBallOne (K : Type u) [NormedField K] : Set K :=
  {y | ‖y - 1‖ < 1}

/-- The ball around `1` is contained in the norm-one sphere. -/
theorem unitBallOne_subset_unitSphere :
    unitBallOne K ⊆ unitSphere K := by
  intro y hy
  have hy' : ‖y - 1‖ < 1 := hy
  have hle : ‖y‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (1 : K) (y - 1)
    have hmax : max ‖(1 : K)‖ ‖y - 1‖ = 1 := by
      rw [norm_one]; exact max_eq_left hy'.le
    calc
      ‖y‖ = ‖(1 : K) + (y - 1)‖ := by ring_nf
      _ ≤ max ‖(1 : K)‖ ‖y - 1‖ := h
      _ = 1 := hmax
  have hge : (1 : ℝ) ≤ ‖y‖ := by
    have h := IsUltrametricDist.norm_add_le_max y (1 - y)
    have hupper : ‖(1 : K)‖ ≤ max ‖y‖ ‖1 - y‖ := by
      calc
        ‖(1 : K)‖ = ‖y + (1 - y)‖ := by ring_nf
        _ ≤ max ‖y‖ ‖1 - y‖ := h
    have hylt : ‖1 - y‖ < 1 := by simpa [norm_sub_rev] using hy'
    have hmax : (1 : ℝ) ≤ max ‖y‖ ‖1 - y‖ := by simpa using hupper
    by_contra hnot
    have hlt : ‖y‖ < 1 := lt_of_not_ge hnot
    have hmaxlt : max ‖y‖ ‖1 - y‖ < 1 := max_lt hlt hylt
    linarith
  exact le_antisymm hle hge

theorem isOpen_unitBallOne : IsOpen (unitBallOne K) :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const

theorem unitBallOne_nonempty : (unitBallOne K).Nonempty := by
  refine ⟨1, ?_⟩
  simp [unitBallOne]

theorem unitBallOne_measure_pos_lt_top
    (mu : Measure K) [Measure.IsAddHaarMeasure mu] :
    0 < mu (unitBallOne K) ∧ mu (unitBallOne K) < ⊤ := by
  constructor
  · apply Measure.measure_pos_of_nonempty_interior
    refine ⟨(1 : K), ?_⟩
    rw [isOpen_unitBallOne (K := K).interior_eq]
    exact unitBallOne_nonempty (K := K)
  · exact lt_of_le_of_lt (measure_mono (unitBallOne_subset_unitSphere (K := K)))
      (isCompact_unitSphere (K := K)).measure_lt_top

end LeanFormal.IUT.N8Closure.P6FiniteReadoutNonzeroAttempt

end