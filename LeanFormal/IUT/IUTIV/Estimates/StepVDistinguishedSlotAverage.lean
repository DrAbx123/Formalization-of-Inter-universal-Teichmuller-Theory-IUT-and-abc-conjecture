import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage

/-!
# Step (v): average the original distinguished-slot bound

IUT IV, Theorem 1.10, pp. 27-28 bounds each collection using the distinguished
slot `i† = j`. Symmetrization preserves the product-weighted average of these
bounds; it need not give an upper bound for each individual collection.

This module supplies the passage from the original pointwise bounds to the
existing procession estimate, without an invariance hypothesis on the volumes
or bounds at every possible distinguished slot.
-/

namespace LeanFormal.IUT.IUTIV.StepVDistinguishedSlotAverage

open scoped BigOperators
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.IUTIV.StepVProcessionAverage

variable {E : Type*} [Fintype E]

/-- Product weights make the sum of the bounds independent of the fixed slot.
The assertion concerns the sum, not the individual bounds. -/
theorem weightedSum_collectionChoiceBound_independent
    (lam : E → ℝ) (l logp iotaL : ℝ) (j : ℕ) (d oq : E → ℝ)
    (first second : Fin (j + 1)) :
    (∑ et : Fin (j + 1) → E,
      collectionChoiceBound l logp iotaL j d oq et first * ∏ i, lam (et i)) =
    ∑ et : Fin (j + 1) → E,
      collectionChoiceBound l logp iotaL j d oq et second * ∏ i, lam (et i) := by
  classical
  have expand (slot : Fin (j + 1)) :
      (∑ et : Fin (j + 1) → E,
        collectionChoiceBound l logp iotaL j d oq et slot * ∏ i, lam (et i)) =
      (-(j : ℝ) ^ 2 / (2 * l) * logp) *
        (∑ et : Fin (j + 1) → E, oq (et slot) * ∏ i, lam (et i)) +
      ∑ et : Fin (j + 1) → E,
        (((∑ i, d (et i)) + 1) * logp + 4 * ((j : ℝ) + 1) * iotaL) *
          ∏ i, lam (et i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro et _
    unfold collectionChoiceBound
    ring
  rw [expand first, expand second,
    iutIVProp17_weightedTupleSum lam oq j first,
    iutIVProp17_weightedTupleSum lam oq j second]

/-- The unsymmetrized bound has exactly the paper's weighted average. -/
theorem weightedAverage_collectionChoiceBound [Nonempty E]
    (lam : E → ℝ) (weights_pos : ∀ e, 0 < lam e)
    (l logp iotaL : ℝ) (l_ne_zero : l ≠ 0)
    (j : ℕ) (d oq : E → ℝ) (slot : Fin (j + 1)) :
    (∑ et : Fin (j + 1) → E,
      collectionChoiceBound l logp iotaL j d oq et slot * ∏ i, lam (et i)) /
      (∑ et : Fin (j + 1) → E, ∏ i, lam (et i)) =
    collectionBound l ((∑ e, d e * logp * lam e) / ∑ e, lam e)
      ((∑ e, oq e * logp * lam e) / ∑ e, lam e) logp iotaL j := by
  classical
  have card_ne_zero : (j : ℝ) + 1 ≠ 0 := by positivity
  have symmetrized_sum :
      (∑ et : Fin (j + 1) → E,
        (1 / ((j : ℝ) + 1) * ∑ i,
          collectionChoiceBound l logp iotaL j d oq et i) * ∏ i, lam (et i)) =
      ∑ et : Fin (j + 1) → E,
        collectionChoiceBound l logp iotaL j d oq et slot * ∏ i, lam (et i) := by
    calc
      _ = 1 / ((j : ℝ) + 1) * ∑ i, ∑ et : Fin (j + 1) → E,
          collectionChoiceBound l logp iotaL j d oq et i * ∏ k, lam (et k) := by
        simp_rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = 1 / ((j : ℝ) + 1) * ∑ _i : Fin (j + 1),
          ∑ et : Fin (j + 1) → E,
            collectionChoiceBound l logp iotaL j d oq et slot * ∏ k, lam (et k) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact weightedSum_collectionChoiceBound_independent lam l logp iotaL j d oq i slot
      _ = _ := by simp [card_ne_zero, Nat.cast_add, Nat.cast_one]
  rw [← symmetrized_sum]
  simp_rw [symmetrize_collectionChoiceBound l logp iotaL l_ne_zero j d oq]
  exact weightedAverage_labelBeta lam weights_pos l logp iotaL l_ne_zero j d oq

/-- It suffices to bound every collection at one fixed distinguished slot.
No bound by the pointwise slot average is required. -/
theorem weightedAverage_le_of_distinguishedBound [Nonempty E]
    (lam : E → ℝ) (weights_pos : ∀ e, 0 < lam e)
    (l logp iotaL : ℝ) (l_ne_zero : l ≠ 0)
    (j : ℕ) (d oq : E → ℝ) (slot : Fin (j + 1))
    (V : (Fin (j + 1) → E) → ℝ)
    (bound : ∀ et, V et ≤ collectionChoiceBound l logp iotaL j d oq et slot) :
    (∑ et : Fin (j + 1) → E, V et * ∏ i, lam (et i)) /
      (∑ et : Fin (j + 1) → E, ∏ i, lam (et i)) ≤
    collectionBound l ((∑ e, d e * logp * lam e) / ∑ e, lam e)
      ((∑ e, oq e * logp * lam e) / ∑ e, lam e) logp iotaL j := by
  classical
  rw [← weightedAverage_collectionChoiceBound lam weights_pos l logp iotaL l_ne_zero
    j d oq slot]
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun et _ =>
      mul_le_mul_of_nonneg_right (bound et)
        (Finset.prod_nonneg fun i _ => (weights_pos (et i)).le)
  · exact Finset.sum_nonneg fun et _ =>
      Finset.prod_nonneg fun i _ => (weights_pos (et i)).le

/-- The procession estimate from the paper's original distinguished-slot
pointwise bounds. For its actual label, choose `slot j = Fin.last j`. -/
theorem processionNormalized_le_of_distinguishedBounds [Nonempty E]
    (n : ℕ) (n_ge_two : 2 ≤ n)
    (lam : E → ℝ) (weights_pos : ∀ e, 0 < lam e)
    (logp iotaL : ℝ) (d oq : E → ℝ)
    (different_nonneg : 0 ≤ (∑ e, d e * logp * lam e) / ∑ e, lam e)
    (logp_nonneg : 0 ≤ logp) (iotaL_nonneg : 0 ≤ iotaL)
    (slot : (j : ℕ) → Fin (j + 1))
    (V : (j : ℕ) → (Fin (j + 1) → E) → ℝ)
    (bound : ∀ j ∈ Finset.Icc 1 n, ∀ et,
      V j et ≤ collectionChoiceBound (2 * (n : ℝ) + 1) logp iotaL j d oq et (slot j)) :
    1 / (n : ℝ) * ∑ j ∈ Finset.Icc 1 n,
      (∑ et : Fin (j + 1) → E, V j et * ∏ i, lam (et i)) /
        (∑ et : Fin (j + 1) → E, ∏ i, lam (et i)) ≤
    (2 * (n : ℝ) + 1 + 1) / 4 *
      ((1 + 4 / (2 * (n : ℝ) + 1)) * ((∑ e, d e * logp * lam e) / (∑ e, lam e)) -
        ((∑ e, oq e * logp * lam e) / (∑ e, lam e)) / 6 +
        (4 / (2 * (n : ℝ) + 1)) * logp + (20 / 3) * iotaL) := by
  classical
  refine le_trans ?_ (processionAverage_le n n_ge_two _ _ logp iotaL
    different_nonneg logp_nonneg iotaL_nonneg)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro j hj
  exact weightedAverage_le_of_distinguishedBound lam weights_pos
    (2 * (n : ℝ) + 1) logp iotaL (by positivity) j d oq (slot j) (V j) (bound j hj)

end LeanFormal.IUT.IUTIV.StepVDistinguishedSlotAverage
