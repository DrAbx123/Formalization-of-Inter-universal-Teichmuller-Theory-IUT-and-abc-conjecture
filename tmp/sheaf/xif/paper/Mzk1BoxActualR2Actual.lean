import tmp.sheaf.xif.paper.Mzk1BoxStepVAverageActual
import Mathlib.Tactic
/-!
# R2: actual ordered-tuple weight `W(t)=∏ λ(t_i)` and distinguished-slot average

Instantiates `Mzk1BoxStepVAverageActual.stepV_weightedAverage_le_of_distinguished`
(itself a wrapper of `StepVDistinguishedSlotAverage.weightedAverage_le_of_distinguishedBound`)
with the actual ordered tuples `t : Fin (j+1) → E` and `W(t) = ∏ i, λ(t_i)`; the
distinguished-slot bound gives the paper `collectionBound` (IV:1585 form).
-/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1BoxActualR2Actual
open LeanFormal.IUT.XiFPaper.Mzk1BoxStepVAverageActual
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.IUTIV.StepVDistinguishedSlotAverage
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
universe u

/-- Actual ordered-tuple weight `W(t) = ∏ i, λ(t_i)`. -/
noncomputable def W {E : Type u} {j : Nat} (lam : E → ℝ) (t : Fin (j + 1) → E) : ℝ :=
  ∏ i, lam (t i)

/-- Distinguished-slot average bound with the actual `W(t)`. -/
theorem actual_weightedAverage_le_of_distinguished
    {E : Type u} [Fintype E] [Nonempty E]
    (lam : E → ℝ) (weights_pos : ∀ e, 0 < lam e)
    (l logp iotaL : ℝ) (l_ne_zero : l ≠ 0)
    (j : Nat) (d oq : E → ℝ) (slot : Fin (j + 1))
    (V : (Fin (j + 1) → E) → ℝ)
    (bound : ∀ t, V t ≤ collectionChoiceBound l logp iotaL j d oq t slot) :
    (∑ t : Fin (j + 1) → E, V t * W lam t) /
      (∑ t : Fin (j + 1) → E, W lam t) ≤
    collectionBound l ((∑ e, d e * logp * lam e) / ∑ e, lam e)
      ((∑ e, oq e * logp * lam e) / ∑ e, lam e) logp iotaL j :=
  stepV_weightedAverage_le_of_distinguished lam weights_pos l logp iotaL l_ne_zero
    j d oq slot V bound

#print axioms actual_weightedAverage_le_of_distinguished
end LeanFormal.IUT.XiFPaper.Mzk1BoxActualR2Actual
end