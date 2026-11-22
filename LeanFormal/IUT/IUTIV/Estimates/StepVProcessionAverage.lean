import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import LeanFormal.IUT.IUTIV.Estimates.Section1

/-!
# IUT IV Theorem 1.10, Step (v): the procession-normalized average over `j`

After the weighted average over the collections `{v_i}` (Proposition 1.7), the
upper bound attached to the label `j` has the form (`IV.txt` L1736–L1741)

`(j + 1)·D - j²/(2l)·Q + S + 4(j + 1)·T`

with `D = log d^K_{vQ}`, `Q = log q_{vQ}`, `S = log s^Q_{vQ}` and
`T = l*_mod · log s^≤_{vQ}`.  Averaging over `j ∈ {1, …, l⋇}`, `l⋇ = (l - 1)/2`,
gives the procession-normalized upper bound (L1745–L1783)

`(l + 5)/4·D - (l + 1)/24·Q + S + (l + 5)·T
   ≤ (l + 1)/4·{(1 + 4/l)·D - Q/6 + (4/l)·S + (20/3)·T}`,

the inequality using `l ≥ 5` and `D, S, T ≥ 0`.  This file proves the exact sum,
the exact average and the final inequality as statements about real numbers;
the arithmetic inputs `D, Q, S, T` are free.
-/

namespace LeanFormal.IUT.IUTIV.StepVProcessionAverage

open Finset

/-- The weighted-average upper bound attached to the label `j` (IV L1736–L1741). -/
noncomputable def collectionBound (l D Q S T : ℝ) (j : ℕ) : ℝ :=
  ((j : ℝ) + 1) * D - (j : ℝ) ^ 2 / (2 * l) * Q + S + 4 * ((j : ℝ) + 1) * T

/-- The sum of the label bounds over `j ∈ {1, …, n}`. -/
theorem sum_collectionBound (l D Q S T : ℝ) (n : ℕ) :
    ∑ j ∈ Icc 1 n, collectionBound l D Q S T j =
      (n : ℝ) * (((n : ℝ) + 3) / 2 * D - ((n : ℝ) + 1) * (2 * n + 1) / (12 * l) * Q + S +
        2 * ((n : ℝ) + 3) * T) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    unfold collectionBound
    push_cast
    ring

/-- **The procession-normalized bound (exact form).**  With `l = 2n + 1`
(`n = l⋇ ≥ 1`), the average over `j ∈ {1, …, n}` of the label bounds equals
`(l + 5)/4·D - (l + 1)/24·Q + S + (l + 5)·T`. -/
theorem processionAverage_eq (n : ℕ) (hn : 1 ≤ n) (D Q S T : ℝ) :
    (1 / (n : ℝ)) * ∑ j ∈ Icc 1 n, collectionBound (2 * n + 1) D Q S T j =
      ((2 * (n : ℝ) + 1) + 5) / 4 * D - ((2 * (n : ℝ) + 1) + 1) / 24 * Q + S +
        ((2 * (n : ℝ) + 1) + 5) * T := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  have hl0 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  rw [sum_collectionBound]
  field_simp
  ring

/-- **The procession-normalized upper bound (IV L1757–L1783).**  For `l = 2n + 1 ≥ 5`
and `D, S, T ≥ 0`,
`(l + 5)/4·D - (l + 1)/24·Q + S + (l + 5)·T
   ≤ (l + 1)/4·{(1 + 4/l)·D - Q/6 + (4/l)·S + (20/3)·T}`. -/
theorem processionAverage_le (n : ℕ) (hn : 2 ≤ n) (D Q S T : ℝ)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    (1 / (n : ℝ)) * ∑ j ∈ Icc 1 n, collectionBound (2 * n + 1) D Q S T j ≤
      ((2 * (n : ℝ) + 1) + 1) / 4 *
        ((1 + 4 / (2 * (n : ℝ) + 1)) * D - Q / 6 + 4 / (2 * (n : ℝ) + 1) * S +
          20 / 3 * T) := by
  rw [processionAverage_eq n (by omega)]
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hdiff : ((2 * (n : ℝ) + 1) + 1) / 4 *
        ((1 + 4 / (2 * (n : ℝ) + 1)) * D - Q / 6 + 4 / (2 * (n : ℝ) + 1) * S +
          20 / 3 * T) -
      (((2 * (n : ℝ) + 1) + 5) / 4 * D - ((2 * (n : ℝ) + 1) + 1) / 24 * Q + S +
        ((2 * (n : ℝ) + 1) + 5) * T) =
      D / (2 * (n : ℝ) + 1) + S / (2 * (n : ℝ) + 1) + (4 * (n : ℝ) - 8) / 3 * T := by
    field_simp
    ring
  have hpos : 0 ≤ D / (2 * (n : ℝ) + 1) + S / (2 * (n : ℝ) + 1) + (4 * (n : ℝ) - 8) / 3 * T := by
    have h1 : 0 ≤ D / (2 * (n : ℝ) + 1) := div_nonneg hD hl.le
    have h2 : 0 ≤ S / (2 * (n : ℝ) + 1) := div_nonneg hS hl.le
    have h3 : 0 ≤ (4 * (n : ℝ) - 8) / 3 * T :=
      mul_nonneg (div_nonneg (by linarith) (by norm_num)) hT
    linarith
  linarith

/-! ## From one collection `{v_i}` to the label bound (IV L1679–L1741) -/

/-- **(R4) rewrite of the exceptional terms (IV L1685–L1696).**  If every
exceptional index `i ∈ I*` satisfies `p ≤ e*_mod·l` and
`log e_i ≤ -3 + 4·log(e*_mod·l)`, then
`∑_{I*} (3 + log e_i) ≤ 4·|I|·ι·log(e*_mod·l)` with `ι = 1` if `p ≤ e*_mod·l`
and `ι = 0` otherwise. -/
theorem exceptionalSum_le_r4 {α : Type*} (I Istar : Finset α) (hsub : Istar ⊆ I)
    (e : α → ℝ) (p el : ℝ) (hel : 1 ≤ el)
    (hR4 : ∀ i ∈ Istar, p ≤ el ∧ Real.log (e i) ≤ -3 + 4 * Real.log el) :
    ∑ i ∈ Istar, (3 + Real.log (e i)) ≤
      4 * (I.card : ℝ) * (if p ≤ el then Real.log el else 0) := by
  have hlog : 0 ≤ Real.log el := Real.log_nonneg hel
  rcases Istar.eq_empty_or_nonempty with h | ⟨i0, hi0⟩
  · subst h
    simp only [sum_empty]
    split_ifs <;> positivity
  · rw [if_pos (hR4 i0 hi0).1]
    calc ∑ i ∈ Istar, (3 + Real.log (e i))
        ≤ ∑ _i ∈ Istar, 4 * Real.log el :=
          sum_le_sum fun i hi => by linarith [(hR4 i hi).2]
      _ = (Istar.card : ℝ) * (4 * Real.log el) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (I.card : ℝ) * (4 * Real.log el) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast card_le_card hsub
      _ = 4 * (I.card : ℝ) * Real.log el := by ring

variable {E : Type*} [Fintype E]

/-- The Step (v) bound for one collection `et` (of size `j + 1`) and one choice of
the slot `i†` carrying `λ = j²/(2l)·ord(q_{v_{i†}})`, after the (R4) rewrite
(IV L1691–L1696): `(-λ + d_I + 1)·log p + 4(j + 1)·ι·l*_mod`. -/
noncomputable def collectionChoiceBound (l logp iotaL : ℝ) (j : ℕ) (d oq : E → ℝ)
    (et : Fin (j + 1) → E) (idag : Fin (j + 1)) : ℝ :=
  (-((j : ℝ) ^ 2 / (2 * l) * oq (et idag)) + ∑ i, d (et i) + 1) * logp +
    4 * ((j : ℝ) + 1) * iotaL

/-- The paper's `β_e` (IV L1717–L1722), with `d_e` the different order,
`oq_e = ord(q_v)` and `iotaL = ι_{vQ}·l*_mod`. -/
noncomputable def labelBeta (l logp iotaL : ℝ) (j : ℕ) (d oq : E → ℝ) (e : E) : ℝ :=
  d e * logp - (j : ℝ) ^ 2 / (2 * l * ((j : ℝ) + 1)) * oq e * logp +
    logp / ((j : ℝ) + 1) + 4 * iotaL

omit [Fintype E] in
/-- **Symmetrization over `i†` (IV L1701–L1709).**  Averaging the collection bound
over the `j + 1` choices of `i†` gives `∑_i β_{e_i}`. -/
theorem symmetrize_collectionChoiceBound (l logp iotaL : ℝ) (hl : l ≠ 0) (j : ℕ)
    (d oq : E → ℝ) (et : Fin (j + 1) → E) :
    (1 / ((j : ℝ) + 1)) * ∑ idag, collectionChoiceBound l logp iotaL j d oq et idag =
      ∑ i, labelBeta l logp iotaL j d oq (et i) := by
  have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
  have hL : ∑ idag, collectionChoiceBound l logp iotaL j d oq et idag =
      ∑ idag : Fin (j + 1), (-((j : ℝ) ^ 2 / (2 * l) * logp) * oq (et idag) +
        (((∑ i, d (et i)) + 1) * logp + 4 * ((j : ℝ) + 1) * iotaL)) :=
    sum_congr rfl fun idag _ => by unfold collectionChoiceBound; ring
  have hR : ∑ i, labelBeta l logp iotaL j d oq (et i) =
      ∑ i : Fin (j + 1), (logp * d (et i) +
        (-((j : ℝ) ^ 2 / (2 * l * ((j : ℝ) + 1)) * logp) * oq (et i) +
          (logp / ((j : ℝ) + 1) + 4 * iotaL))) :=
    sum_congr rfl fun i _ => by unfold labelBeta; ring
  rw [hL, hR]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  ring
/-- **Weighted average over collections (Prop 1.7, IV L1730–L1741).**  With
weights `λ^Π`, the weighted average of `∑_i β_{e_i}` equals the label bound
`(j + 1)·D - j²/(2l)·Q + log p + 4(j + 1)·ι·l*_mod`, where `D` and `Q` are the
`λ`-weighted averages of `d_e·log p` and `ord(q_e)·log p`. -/
theorem weightedAverage_labelBeta [Nonempty E] (lam : E → ℝ) (hlam : ∀ e, 0 < lam e)
    (l logp iotaL : ℝ) (hl : l ≠ 0) (j : ℕ) (d oq : E → ℝ) :
    (∑ et : Fin (j + 1) → E, (∑ i, labelBeta l logp iotaL j d oq (et i)) * ∏ i, lam (et i)) /
        (∑ et : Fin (j + 1) → E, ∏ i, lam (et i)) =
      collectionBound l ((∑ e, d e * logp * lam e) / ∑ e, lam e)
        ((∑ e, oq e * logp * lam e) / ∑ e, lam e) logp iotaL j := by
  rw [LeanFormal.IUT.IUTIV.Estimates.iutIVProp17_value lam (labelBeta l logp iotaL j d oq) hlam j]
  have hE : (∑ e, lam e) ≠ 0 :=
    (sum_pos (fun e _ => hlam e) univ_nonempty).ne'
  have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
  unfold LeanFormal.IUT.IUTIV.Estimates.iutIVProp17_betaAvg
  have hS : ∑ e, labelBeta l logp iotaL j d oq e * lam e =
      (∑ e, d e * logp * lam e) +
        (-((j : ℝ) ^ 2 / (2 * l * ((j : ℝ) + 1)))) * (∑ e, oq e * logp * lam e) +
          (logp / ((j : ℝ) + 1) + 4 * iotaL) * (∑ e, lam e) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun e _ => by unfold labelBeta; ring
  rw [hS]
  unfold collectionBound
  push_cast
  generalize (∑ e, d e * logp * lam e) = A
  generalize (∑ e, oq e * logp * lam e) = B
  generalize (∑ e, lam e) = Λ at hE ⊢
  field_simp
  ring
/-- **Collection bounds ⇒ label bound.**  If the (normalized) hull log-volume
`V et` of every collection is bounded by its symmetrized Step (v) bound, then the
`λ^Π`-weighted average of `V` is at most the label bound of `collectionBound`. -/
theorem weightedAverage_le_collectionBound [Nonempty E] (lam : E → ℝ)
    (hlam : ∀ e, 0 < lam e) (l logp iotaL : ℝ) (hl : l ≠ 0) (j : ℕ) (d oq : E → ℝ)
    (V : (Fin (j + 1) → E) → ℝ)
    (hV : ∀ et, V et ≤ (1 / ((j : ℝ) + 1)) *
      ∑ idag, collectionChoiceBound l logp iotaL j d oq et idag) :
    (∑ et : Fin (j + 1) → E, V et * ∏ i, lam (et i)) /
        (∑ et : Fin (j + 1) → E, ∏ i, lam (et i)) ≤
      collectionBound l ((∑ e, d e * logp * lam e) / ∑ e, lam e)
        ((∑ e, oq e * logp * lam e) / ∑ e, lam e) logp iotaL j := by
  rw [← weightedAverage_labelBeta lam hlam l logp iotaL hl j d oq]
  have hden : 0 < ∑ et : Fin (j + 1) → E, ∏ i, lam (et i) :=
    sum_pos (fun et _ => prod_pos fun i _ => hlam (et i)) univ_nonempty
  apply div_le_div_of_nonneg_right _ hden.le
  apply sum_le_sum
  intro et _
  apply mul_le_mul_of_nonneg_right _ (prod_pos fun i _ => hlam (et i)).le
  rw [← symmetrize_collectionChoiceBound l logp iotaL hl]
  exact hV et

/-- **IUT IV Theorem 1.10, Step (v) at one `vQ ∈ V_Q^dst` (IV L1679–L1783).**
Let `V j et` be the normalized hull log-volume attached to the label `j` and the
collection `et`, bounded by its symmetrized Step (v) bound (after (R4)).  Then the
procession-normalized average over `j ∈ {1, …, l⋇}` of the `λ^Π`-weighted averages
is at most
`(l + 1)/4·{(1 + 4/l)·D - Q/6 + (4/l)·log p + (20/3)·ι·l*_mod}`,
with `D, Q` the weighted averages of `d_e·log p` and `ord(q_e)·log p`,
`l = 2l⋇ + 1 ≥ 5`. -/
theorem processionNormalized_le_of_collectionBounds [Nonempty E] (n : ℕ) (hn : 2 ≤ n)
    (lam : E → ℝ) (hlam : ∀ e, 0 < lam e) (logp iotaL : ℝ) (d oq : E → ℝ)
    (hD : 0 ≤ (∑ e, d e * logp * lam e) / ∑ e, lam e) (hS : 0 ≤ logp) (hT : 0 ≤ iotaL)
    (V : (j : ℕ) → (Fin (j + 1) → E) → ℝ)
    (hV : ∀ j ∈ Icc 1 n, ∀ et, V j et ≤ (1 / ((j : ℝ) + 1)) *
      ∑ idag, collectionChoiceBound (2 * n + 1) logp iotaL j d oq et idag) :
    (1 / (n : ℝ)) * ∑ j ∈ Icc 1 n,
        (∑ et : Fin (j + 1) → E, V j et * ∏ i, lam (et i)) /
          (∑ et : Fin (j + 1) → E, ∏ i, lam (et i)) ≤
      ((2 * (n : ℝ) + 1) + 1) / 4 *
        ((1 + 4 / (2 * (n : ℝ) + 1)) * ((∑ e, d e * logp * lam e) / ∑ e, lam e) -
          ((∑ e, oq e * logp * lam e) / ∑ e, lam e) / 6 +
          4 / (2 * (n : ℝ) + 1) * logp + 20 / 3 * iotaL) := by
  have hl : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hsum : ∑ j ∈ Icc 1 n,
        (∑ et : Fin (j + 1) → E, V j et * ∏ i, lam (et i)) /
          (∑ et : Fin (j + 1) → E, ∏ i, lam (et i)) ≤
      ∑ j ∈ Icc 1 n, collectionBound (2 * n + 1)
        ((∑ e, d e * logp * lam e) / ∑ e, lam e)
        ((∑ e, oq e * logp * lam e) / ∑ e, lam e) logp iotaL j :=
    sum_le_sum fun j hj =>
      weightedAverage_le_collectionBound lam hlam (2 * n + 1) logp iotaL hl j d oq (V j)
        (hV j hj)
  have hn0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  calc (1 / (n : ℝ)) * ∑ j ∈ Icc 1 n,
        (∑ et : Fin (j + 1) → E, V j et * ∏ i, lam (et i)) /
          (∑ et : Fin (j + 1) → E, ∏ i, lam (et i))
      ≤ (1 / (n : ℝ)) * ∑ j ∈ Icc 1 n, collectionBound (2 * n + 1)
        ((∑ e, d e * logp * lam e) / ∑ e, lam e)
        ((∑ e, oq e * logp * lam e) / ∑ e, lam e) logp iotaL j :=
        mul_le_mul_of_nonneg_left hsum hn0
    _ ≤ _ := processionAverage_le n hn _ _ _ _ hD hS hT

end LeanFormal.IUT.IUTIV.StepVProcessionAverage
