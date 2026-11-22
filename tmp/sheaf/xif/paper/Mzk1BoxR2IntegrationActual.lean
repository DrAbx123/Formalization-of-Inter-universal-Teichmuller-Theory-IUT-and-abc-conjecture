import tmp.sheaf.xif.paper.Mzk1BoxR2PerRowActual
import tmp.sheaf.xif.paper.Mzk1BoxActualR2Actual
import Mathlib.Tactic
/-!
# R2 integration: distinguished-slot average via the per-row IV:1585 equality

Combines `Mzk1BoxActualR2Actual.actual_weightedAverage_le_of_distinguished` with
`Mzk1BoxR2PerRowActual.perRow_eq_collectionBound`: the choice-bound row average is
exactly `collectionBound`, so the actual weighted average satisfies IV:1585.
-/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1BoxR2IntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxActualR2Actual
open LeanFormal.IUT.XiFPaper.Mzk1BoxR2PerRowActual
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.IUTIV.StepVDistinguishedSlotAverage
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
universe u

theorem W_nonneg {E : Type u} {j : Nat} (lam : E → ℝ) (h : ∀ e, 0 < lam e)
    (t : Fin (j + 1) → E) : 0 ≤ W lam t := by
  unfold W
  exact Finset.prod_nonneg (fun i _ => le_of_lt (h _))

theorem W_sum_pos {E : Type u} [Fintype E] [Nonempty E] {j : Nat}
    (lam : E → ℝ) (h : ∀ e, 0 < lam e) : 0 < ∑ t : Fin (j + 1) → E, W lam t := by
  classical
  refine Finset.sum_pos (fun t _ => ?_) Finset.univ_nonempty
  unfold W
  exact Finset.prod_pos (fun i _ => h _)

theorem actual_weightedAverage_le_collectionBound_via_perRow
    {E : Type u} [Fintype E] [Nonempty E]
    (lam : E → ℝ) (weights_pos : ∀ e, 0 < lam e)
    (l logp iotaL : ℝ) (l_ne_zero : l ≠ 0)
    (j : Nat) (d oq : E → ℝ) (slot : Fin (j + 1))
    (V : (Fin (j + 1) → E) → ℝ)
    (bound : ∀ t, V t ≤ collectionChoiceBound l logp iotaL j d oq t slot) :
    (∑ t : Fin (j + 1) → E, V t * W lam t) /
      (∑ t : Fin (j + 1) → E, W lam t) ≤
    collectionBound l ((∑ e, d e * logp * lam e) / ∑ e, lam e)
      ((∑ e, oq e * logp * lam e) / ∑ e, lam e) logp iotaL j := by
  have hden : 0 < ∑ t : Fin (j + 1) → E, W lam t := W_sum_pos lam weights_pos
  have hsum : ∑ t : Fin (j + 1) → E, V t * W lam t ≤
      ∑ t : Fin (j + 1) → E,
        collectionChoiceBound l logp iotaL j d oq t slot * W lam t :=
    Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_right (bound t) (W_nonneg lam weights_pos t))
  calc (∑ t : Fin (j + 1) → E, V t * W lam t) /
        (∑ t : Fin (j + 1) → E, W lam t)
      ≤ (∑ t : Fin (j + 1) → E,
          collectionChoiceBound l logp iotaL j d oq t slot * W lam t) /
          (∑ t : Fin (j + 1) → E, W lam t) := by
        exact div_le_div_of_nonneg_right hsum (le_of_lt hden)
    _ = collectionBound l ((∑ e, d e * logp * lam e) / ∑ e, lam e)
          ((∑ e, oq e * logp * lam e) / ∑ e, lam e) logp iotaL j :=
        perRow_eq_collectionBound lam weights_pos l logp iotaL l_ne_zero j d oq slot

#print axioms actual_weightedAverage_le_collectionBound_via_perRow
end LeanFormal.IUT.XiFPaper.Mzk1BoxR2IntegrationActual
end