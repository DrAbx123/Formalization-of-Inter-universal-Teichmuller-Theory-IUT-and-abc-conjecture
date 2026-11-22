/- O6 / M2: explicit coefficient bound B(d0) for henry's P3.

Reuse: Mzk1G1O6M2PinValueActual.coeffBound/norm_eval_le_coeffBound/pinValue_avoid.
-/
import tmp.sheaf.xif.paper.Mzk1G1O6M2PinValueActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinCoeffBoundActual

open LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinValueActual

/-- Coeff bound by (deg+1)*M when all coefficient norms are at most M. -/
theorem coeffBound_le_card_mul_max {f : ℚ[X]} {M : ℝ}
    (hM : ∀ i, ‖(f.coeff i : ℂ)‖ ≤ M) :
    coeffBound f ≤ (f.natDegree + 1 : ℝ) * M := by
  unfold coeffBound
  calc (∑ i ∈ Finset.range (f.natDegree + 1), ‖(f.coeff i : ℂ)‖)
      ≤ ∑ i ∈ Finset.range (f.natDegree + 1), M := by
        apply Finset.sum_le_sum
        intro i hi
        exact hM i
    _ = (f.natDegree + 1 : ℝ) * M := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- Beta-avoidance with the explicit B(d0) = (deg+1)*M bound. -/
theorem pinValue_avoid_of_coeff_bound {f : ℚ[X]} {S : Finset ℂ} {β : ℂ} {M : ℝ}
    (hS : ∀ s ∈ S, ‖s‖ ≤ 1) (hM : ∀ i, ‖(f.coeff i : ℂ)‖ ≤ M)
    (hβ : ((f.natDegree + 1 : ℝ) * M) < ‖(f.map (algebraMap ℚ ℂ)).eval β‖) :
    (f.map (algebraMap ℚ ℂ)).eval β ∉ S.image (fun s => (f.map (algebraMap ℚ ℂ)).eval s) := by
  apply pinValue_avoid hS
  exact lt_of_le_of_lt (coeffBound_le_card_mul_max hM) hβ

#print axioms coeffBound_le_card_mul_max
#print axioms pinValue_avoid_of_coeff_bound
end LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinCoeffBoundActual
