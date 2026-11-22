/- Hensel near-root existence for a complete ultrametric normed field (integral form),
ported from Mathlib's Z_p Hensel lemma.  No PadicInt and no completion root.

Hypotheses: f : L[X] has integral coefficients (all norms ≤ 1), the point a is
integral (‖a‖ ≤ 1), and ‖f(a)‖ < ‖f'(a)‖².  Then a root b exists with
‖b - a‖ < ‖f'(a)‖, and any two roots in that open ball coincide. -/
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.MetricSpace.Cauchy

noncomputable section
open Filter Topology
open scoped Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1LpHenselNearRootActual

open Polynomial

variable {L : Type*} [NormedField L] [IsUltrametricDist L]

/-! ## Elementary bounds -/

theorem norm_add_le_max' (x y : L) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  have h := IsUltrametricDist.dist_triangle_max (x + y) x 0
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h
  simpa [show (x + y) - x = y by ring, max_comm] using h

theorem norm_mul_le_one {x y : L} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]
  nlinarith [norm_nonneg x, norm_nonneg y]

theorem norm_pow_le_one {x : L} (hx : ‖x‖ ≤ 1) (n : Nat) : ‖x ^ n‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact norm_mul_le_one ih hx

theorem norm_add_eq_left_of_norm_lt {x y : L} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  refine le_antisymm ((norm_add_le_max' x y).trans (le_of_eq (max_eq_left h.le))) ?_
  rcases le_total ‖x + y‖ ‖y‖ with hle | hlt
  · have hx : ‖x‖ ≤ max ‖x + y‖ ‖y‖ := by
      have h' := IsUltrametricDist.dist_triangle_max x (-y) 0
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h'
      simpa [show x - -y = x + y by ring, max_comm] using h'
    rw [max_eq_right hle] at hx
    linarith
  · have hx : ‖x‖ ≤ max ‖x + y‖ ‖y‖ := by
      have h' := IsUltrametricDist.dist_triangle_max x (-y) 0
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h'
      simpa [show x - -y = x + y by ring, max_comm] using h'
    rw [max_eq_left hlt] at hx
    exact hx

theorem norm_sum_le_of_bound {ι : Type*} (s : Finset ι) (g : ι → L) {C : Real} (hC : 0 ≤ C)
    (h : ∀ i ∈ s, ‖g i‖ ≤ C) : ‖∑ i ∈ s, g i‖ ≤ C := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hC
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine (norm_add_le_max' _ _).trans (max_le ?_ ?_)
      · exact h a (Finset.mem_insert_self a s)
      · exact ih fun i hi => h i (Finset.mem_insert_of_mem hi)

theorem norm_eval_le_one_of_coeff_le_one {f : L[X]} (hf : ∀ n, ‖f.coeff n‖ ≤ 1)
    {z : L} (hz : ‖z‖ ≤ 1) : ‖f.eval z‖ ≤ 1 := by
  rw [eval_eq_sum]
  unfold Polynomial.sum
  exact norm_sum_le_of_bound f.support (fun e => f.coeff e * z ^ e) zero_le_one
    (fun e _ => norm_mul_le_one (hf e) (norm_pow_le_one hz e))

theorem norm_coeff_derivative_le_one {f : L[X]} (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (n : Nat) :
    ‖f.derivative.coeff n‖ ≤ 1 := by
  rw [coeff_derivative]
  refine norm_mul_le_one (hf (n + 1)) ?_
  simpa [Nat.cast_add, Nat.cast_one] using IsUltrametricDist.norm_natCast_le_one L (n + 1)

theorem norm_derivative_eval_le_one {f : L[X]} (hf : ∀ n, ‖f.coeff n‖ ≤ 1)
    {z : L} (hz : ‖z‖ ≤ 1) : ‖f.derivative.eval z‖ ≤ 1 :=
  norm_eval_le_one_of_coeff_le_one (norm_coeff_derivative_le_one hf) hz

/-! ## Self-contained quadratic Taylor data -/

/-- The quadratic Taylor quotient: (x + y)^n = x^n + n x^(n-1) y + Q_n(x,y) y^2. -/
noncomputable def powAddQ (x y : L) : Nat → L
  | 0 => 0
  | 1 => 0
  | (n + 2) => x * powAddQ x y (n + 1) + ((n + 1 : Nat) : L) * x ^ n + powAddQ x y (n + 1) * y

theorem powAddQ_spec (x y : L) :
    ∀ n : Nat, (x + y) ^ n = x ^ n + (n : L) * x ^ (n - 1) * y + powAddQ x y n * y ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 => simp [powAddQ]
      | 1 => norm_num [powAddQ]
      | (k + 2) =>
          have h1 := ih (k + 1) (by omega)
          have h2 : (x + y) ^ (k + 2) = (x + y) * (x + y) ^ (k + 1) := by ring
          rw [h2, h1]
          simp only [powAddQ, Nat.add_sub_cancel]
          push_cast
          ring

theorem powAddQ_norm_le_one (x y : L) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∀ n : Nat, ‖powAddQ x y n‖ ≤ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 => simp [powAddQ]
      | 1 => simp [powAddQ]
      | (k + 2) =>
          have hk : ‖powAddQ x y (k + 1)‖ ≤ 1 := ih (k + 1) (by omega)
          have hval : powAddQ x y (k + 2) =
              x * powAddQ x y (k + 1) + ((k + 1 : Nat) : L) * x ^ k +
                powAddQ x y (k + 1) * y := rfl
          rw [hval]
          refine (norm_add_le_max' _ _).trans (max_le ?_ ?_)
          · refine (norm_add_le_max' _ _).trans (max_le ?_ ?_)
            · exact norm_mul_le_one hx hk
            · exact norm_mul_le_one (IsUltrametricDist.norm_natCast_le_one L (k + 1))
                (norm_pow_le_one hx k)
          · exact norm_mul_le_one hk hy

/-- The quotient for x^n - y^n = Q_n(x,y) (x - y). -/
noncomputable def powSubQ (x y : L) : Nat → L
  | 0 => 0
  | 1 => 1
  | (n + 2) => powSubQ x y (n + 1) * x + y ^ (n + 1)

theorem powSubQ_spec (x y : L) : ∀ n : Nat, x ^ n - y ^ n = powSubQ x y n * (x - y) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 => simp [powSubQ]
      | 1 => norm_num [powSubQ]
      | (k + 2) =>
          have h1 := ih (k + 1) (by omega)
          have hval : powSubQ x y (k + 2) = powSubQ x y (k + 1) * x + y ^ (k + 1) := rfl
          rw [hval]
          calc x ^ (k + 2) - y ^ (k + 2)
              = x * (x ^ (k + 1) - y ^ (k + 1)) + y ^ (k + 1) * (x - y) := by ring
            _ = x * (powSubQ x y (k + 1) * (x - y)) + y ^ (k + 1) * (x - y) := by rw [h1]
            _ = (powSubQ x y (k + 1) * x + y ^ (k + 1)) * (x - y) := by ring

theorem powSubQ_norm_le_one (x y : L) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∀ n : Nat, ‖powSubQ x y n‖ ≤ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 => simp [powSubQ]
      | 1 => simp [powSubQ]
      | (k + 2) =>
          have hk : ‖powSubQ x y (k + 1)‖ ≤ 1 := ih (k + 1) (by omega)
          have hval : powSubQ x y (k + 2) = powSubQ x y (k + 1) * x + y ^ (k + 1) := rfl
          rw [hval]
          exact (norm_add_le_max' _ _).trans
            (max_le (norm_mul_le_one hk hx) (norm_pow_le_one hy (k + 1)))

/-- The quotient of f(x) - f(y) by x - y. -/
noncomputable def evalSubQuot (f : L[X]) (x y : L) : L :=
  f.sum fun i r => r * powSubQ x y i

theorem eval_sub_eval_eq (f : L[X]) (x y : L) :
    f.eval x - f.eval y = evalSubQuot f x y * (x - y) := by
  rw [eval_eq_sum, eval_eq_sum]
  unfold evalSubQuot Polynomial.sum
  rw [← Finset.sum_sub_distrib]
  trans f.support.sum (fun i => (f.coeff i * powSubQ x y i) * (x - y))
  · apply Finset.sum_congr rfl
    intro i _
    calc f.coeff i * x ^ i - f.coeff i * y ^ i
        = f.coeff i * (x ^ i - y ^ i) := by ring
      _ = f.coeff i * (powSubQ x y i * (x - y)) := by rw [powSubQ_spec]
      _ = (f.coeff i * powSubQ x y i) * (x - y) := by ring
  · rw [Finset.sum_mul]

theorem evalSubQuot_norm_le_one {f : L[X]} (hf : ∀ n, ‖f.coeff n‖ ≤ 1) {x y : L}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖evalSubQuot f x y‖ ≤ 1 := by
  unfold evalSubQuot Polynomial.sum
  exact norm_sum_le_of_bound f.support (fun i => f.coeff i * powSubQ x y i) zero_le_one
    (fun i _ => norm_mul_le_one (hf i) (powSubQ_norm_le_one x y hx hy i))

theorem norm_eval_sub_eval_le {f : L[X]} (hf : ∀ n, ‖f.coeff n‖ ≤ 1) {x y : L}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖f.eval x - f.eval y‖ ≤ ‖x - y‖ := by
  rw [eval_sub_eval_eq, norm_mul]
  exact (mul_le_mul_of_nonneg_right (evalSubQuot_norm_le_one hf hx hy)
    (norm_nonneg _)).trans_eq (one_mul _)

/-- Explicit quadratic Taylor identity with our quotient `powAddQ`. -/
theorem eval_taylor_aux (f : L[X]) (x y : L) :
    f.eval (x + y) = ((f.sum fun e a => a * x ^ e) +
      (f.sum fun e a => a * (e : L) * x ^ (e - 1) * y)) +
        f.sum fun e a => a * powAddQ x y e * y ^ 2 := by
  rw [eval_eq_sum]
  have hcongr : f.sum (fun e a => a * (x + y) ^ e) =
      f.sum (fun e a => a * x ^ e +
        (a * (e : L) * x ^ (e - 1) * y + a * powAddQ x y e * y ^ 2)) := by
    unfold Polynomial.sum
    exact Finset.sum_congr rfl fun e _ => by
      change f.coeff e * (x + y) ^ e = f.coeff e * x ^ e +
        (f.coeff e * (e : L) * x ^ (e - 1) * y + f.coeff e * powAddQ x y e * y ^ 2)
      rw [powAddQ_spec]
      ring
  rw [hcongr]
  simp only [Polynomial.sum_add]
  ring

/-- Quadratic Taylor expansion with integral remainder. -/
theorem exists_taylor_remainder {f : L[X]} (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (x y : L)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∃ q : L, ‖q‖ ≤ 1 ∧ f.eval (x + y) = f.eval x + f.derivative.eval x * y + q * y ^ 2 := by
  refine ⟨f.sum fun e a => a * powAddQ x y e, ?_, ?_⟩
  · unfold Polynomial.sum
    exact norm_sum_le_of_bound f.support (fun e => f.coeff e * powAddQ x y e) zero_le_one
      (fun e _ => norm_mul_le_one (hf e) (powAddQ_norm_le_one x y hx hy e))
  · rw [eval_taylor_aux, eval_eq_sum, derivative_eval]
    simp only [Polynomial.sum]
    rw [← Finset.sum_mul, ← Finset.sum_mul]

/-! ## Uniqueness in the open ball -/

section Unique

variable (f : L[X]) (a : L)

theorem deriv_eval_le_one (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1) :
    ‖f.derivative.eval a‖ ≤ 1 :=
  norm_derivative_eval_le_one hf ha

theorem deriv_norm_pos (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) :
    0 < ‖f.derivative.eval a‖ := by
  have hpos : 0 < ‖f.derivative.eval a‖ ^ 2 :=
    lt_of_le_of_lt (norm_nonneg (f.eval a)) hnorm
  rcases (norm_nonneg (f.derivative.eval a)).lt_or_eq with h | h
  · exact h
  · rw [← h] at hpos
    simp at hpos

theorem root_integral (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    {b : L} (hb : ‖b - a‖ < ‖f.derivative.eval a‖) : ‖b‖ ≤ 1 := by
  have h : ‖b‖ = ‖a + (b - a)‖ := by rw [add_sub_cancel]
  rw [h]
  refine (norm_add_le_max' _ _).trans (max_le ha ?_)
  exact hb.le.trans (deriv_eval_le_one f a hf ha)

theorem deriv_root_norm (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2)
    {b : L} (hb : ‖b - a‖ < ‖f.derivative.eval a‖) :
    ‖f.derivative.eval b‖ = ‖f.derivative.eval a‖ := by
  have hb_int : ‖b‖ ≤ 1 := root_integral f a hf ha hb
  have hdist : ‖f.derivative.eval b - f.derivative.eval a‖ ≤ ‖b - a‖ :=
    norm_eval_sub_eval_le (f := f.derivative) (norm_coeff_derivative_le_one hf) hb_int ha
  have hlt : ‖f.derivative.eval b - f.derivative.eval a‖ < ‖f.derivative.eval a‖ :=
    lt_of_le_of_lt hdist hb
  calc ‖f.derivative.eval b‖
      = ‖f.derivative.eval a + (f.derivative.eval b - f.derivative.eval a)‖ := by ring_nf
    _ = ‖f.derivative.eval a‖ := norm_add_eq_left_of_norm_lt hlt

/-- Two roots in the open ball of radius ‖f'(a)‖ coincide. -/
theorem eq_of_roots_close_aux (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2)
    {b1 b2 : L} (h1 : f.eval b1 = 0) (h2 : f.eval b2 = 0)
    (hb1 : ‖b1 - a‖ < ‖f.derivative.eval a‖)
    (hb2 : ‖b2 - a‖ < ‖f.derivative.eval a‖) : b1 = b2 := by
  by_contra hne
  have hb1_int : ‖b1‖ ≤ 1 := root_integral f a hf ha hb1
  have hb2_int : ‖b2‖ ≤ 1 := root_integral f a hf ha hb2
  have hdiff_int : ‖b1 - b2‖ ≤ 1 := by
    have h := (norm_add_le_max' b1 (-b2)).trans (max_le hb1_int (by simpa using hb2_int))
    simpa [sub_eq_add_neg] using h
  have hb2_deriv : ‖f.derivative.eval b2‖ = ‖f.derivative.eval a‖ :=
    deriv_root_norm f a hf ha hnorm hb2
  obtain ⟨q, hqle, hq⟩ := exists_taylor_remainder hf b2 (b1 - b2) hb2_int hdiff_int
  have hzero : f.derivative.eval b2 * (b1 - b2) + q * (b1 - b2) ^ 2 = 0 := by
    have h := hq
    rw [show b2 + (b1 - b2) = b1 by ring] at h
    rw [h1, h2] at h
    simpa only [zero_add] using h.symm
  have hd : b1 - b2 ≠ 0 := sub_ne_zero.mpr hne
  have hfac : (f.derivative.eval b2 + q * (b1 - b2)) * (b1 - b2) = 0 := by
    linear_combination hzero
  have hderiv_eq : f.derivative.eval b2 = -(q * (b1 - b2)) := by
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hfac with h | h
    · linear_combination h
    · exact absurd h hd
  have hbound : ‖f.derivative.eval a‖ ≤ ‖b1 - b2‖ := by
    rw [← hb2_deriv, hderiv_eq, norm_neg, norm_mul]
    exact (mul_le_mul_of_nonneg_right hqle (norm_nonneg _)).trans_eq (one_mul _)
  have hupper : ‖b1 - b2‖ ≤ max ‖b1 - a‖ ‖b2 - a‖ := by
    have heq : (b1 - a) + -(b2 - a) = b1 - b2 := by ring
    calc ‖b1 - b2‖ = ‖(b1 - a) + -(b2 - a)‖ := by rw [heq]
      _ ≤ max ‖b1 - a‖ ‖-(b2 - a)‖ := norm_add_le_max' _ _
      _ = max ‖b1 - a‖ ‖b2 - a‖ := by rw [norm_neg]
  have hmax : max ‖b1 - a‖ ‖b2 - a‖ < ‖f.derivative.eval a‖ := max_lt hb1 hb2
  exact absurd (le_trans hbound hupper) (not_le.mpr hmax)

end Unique

/-! ## The Newton iteration -/

noncomputable def newtonStep (f : L[X]) (z : L) : L := z - f.eval z / f.derivative.eval z

noncomputable def newtonSeq (f : L[X]) (a : L) (n : Nat) : L := (newtonStep f)^[n] a

theorem newtonSeq_zero (f : L[X]) (a : L) : newtonSeq f a 0 = a := rfl

theorem newtonSeq_succ (f : L[X]) (a : L) (n : Nat) :
    newtonSeq f a (n + 1) = newtonStep f (newtonSeq f a n) :=
  Function.iterate_succ_apply' (newtonStep f) n a

theorem newtonStep_eq (f : L[X]) (z : L) :
    newtonStep f z = z - f.eval z / f.derivative.eval z := rfl

section Main

variable [CompleteSpace L]

variable (f : L[X]) (a : L)

/-- Contraction factor T = ‖f(a)‖ / ‖f'(a)‖^2. -/
noncomputable def T : Real := ‖f.eval a‖ / ‖f.derivative.eval a‖ ^ 2

theorem T_nonneg : 0 ≤ T f a := div_nonneg (norm_nonneg _) (sq_nonneg _)

theorem deriv_sq_norm_pos (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) :
    0 < ‖f.derivative.eval a‖ ^ 2 :=
  lt_of_le_of_lt (norm_nonneg (f.eval a)) hnorm

theorem T_lt_one (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) : T f a < 1 := by
  rw [T]
  exact (div_lt_one (deriv_sq_norm_pos f a hnorm)).2 hnorm

theorem T_pow_lt_one' (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) (n : Nat) :
    T f a ^ 2 ^ n < 1 :=
  pow_lt_one₀ (T_nonneg f a) (T_lt_one f a hnorm) (pow_ne_zero _ two_ne_zero)

/-- Newton invariant. -/
def ih (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) (n : Nat) (z : L) : Prop :=
  ‖f.derivative.eval z‖ = ‖f.derivative.eval a‖ ∧
    ‖f.eval z‖ ≤ ‖f.derivative.eval a‖ ^ 2 * T f a ^ 2 ^ n ∧ ‖z‖ ≤ 1

theorem ih_0 (hf : ∀ n, ‖f.coeff n‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) (ha : ‖a‖ ≤ 1) :
    ih f a hnorm 0 a := by
  refine ⟨rfl, ?_, ha⟩
  have hR : ‖f.derivative.eval a‖ ≠ 0 := (deriv_norm_pos f a hnorm).ne'
  have h : ‖f.derivative.eval a‖ ^ 2 * (‖f.eval a‖ / ‖f.derivative.eval a‖ ^ 2) =
      ‖f.eval a‖ := by
    field_simp
  rw [T, pow_zero, pow_one]
  exact le_of_eq h.symm

theorem eval_div_deriv_le_one (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2)
    {n : Nat} {z : L} (hz : ih f a hnorm n z) :
    ‖f.eval z / f.derivative.eval z‖ ≤ 1 := by
  rw [norm_div, hz.1, div_le_one (deriv_norm_pos f a hnorm)]
  have hTle : T f a ^ 2 ^ n ≤ 1 := (T_pow_lt_one' f a hnorm n).le
  have hRle : ‖f.derivative.eval a‖ ≤ 1 := norm_derivative_eval_le_one hf ha
  have hR0 : 0 ≤ ‖f.derivative.eval a‖ := norm_nonneg _
  have h1 : ‖f.derivative.eval a‖ ^ 2 * T f a ^ 2 ^ n ≤ ‖f.derivative.eval a‖ ^ 2 :=
    mul_le_of_le_one_right (sq_nonneg _) hTle
  have h2 : ‖f.derivative.eval a‖ ^ 2 ≤ ‖f.derivative.eval a‖ := by nlinarith
  linarith [hz.2.1]

/-- One Newton step preserves the invariant. -/
theorem ih_newtonStep (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2)
    {n : Nat} {z : L} (hz : ih f a hnorm n z) :
    ih f a hnorm (n + 1) (newtonStep f z) := by
  rw [newtonStep_eq]
  set z1 : L := f.eval z / f.derivative.eval z with hz1def
  have hz1le : ‖z1‖ ≤ 1 := eval_div_deriv_le_one f a hf ha hnorm hz
  have hz1norm : ‖z1‖ = ‖f.eval z‖ / ‖f.derivative.eval a‖ := by
    rw [hz1def, norm_div, hz.1]
  have hzint : ‖z‖ ≤ 1 := hz.2.2
  have hz'int : ‖z - z1‖ ≤ 1 := by
    have := (norm_add_le_max' z (-z1)).trans (max_le hzint (by simpa using hz1le))
    simpa [sub_eq_add_neg] using this
  have hRpos : 0 < ‖f.derivative.eval a‖ := deriv_norm_pos f a hnorm
  have hderiv_dist : ‖f.derivative.eval (z - z1) - f.derivative.eval z‖ <
      ‖f.derivative.eval a‖ := by
    calc ‖f.derivative.eval (z - z1) - f.derivative.eval z‖ ≤ ‖(z - z1) - z‖ :=
          norm_eval_sub_eval_le (f := f.derivative) (norm_coeff_derivative_le_one hf)
            hz'int hzint
      _ = ‖z1‖ := by rw [sub_sub_cancel_left, norm_neg]
      _ = ‖f.eval z‖ / ‖f.derivative.eval a‖ := hz1norm
      _ ≤ (‖f.derivative.eval a‖ ^ 2 * T f a ^ 2 ^ n) / ‖f.derivative.eval a‖ :=
          div_le_div_of_nonneg_right hz.2.1 hRpos.le
      _ = ‖f.derivative.eval a‖ * T f a ^ 2 ^ n := by field_simp
      _ < ‖f.derivative.eval a‖ := by
          nlinarith [hRpos, T_pow_lt_one' f a hnorm n]
  have hderiv_eq : ‖f.derivative.eval (z - z1)‖ = ‖f.derivative.eval a‖ := by
    calc ‖f.derivative.eval (z - z1)‖
        = ‖f.derivative.eval z + (f.derivative.eval (z - z1) - f.derivative.eval z)‖ := by
          ring_nf
      _ = ‖f.derivative.eval z‖ := norm_add_eq_left_of_norm_lt (by rwa [hz.1])
      _ = ‖f.derivative.eval a‖ := hz.1
  have hdzne : f.derivative.eval z ≠ 0 := by
    intro h
    rw [← hz.1, h, norm_zero] at hRpos
    exact lt_irrefl 0 hRpos
  obtain ⟨q, hqle, hq⟩ :=
    exists_taylor_remainder hf z (-z1) hzint (by simpa using hz1le)
  have hcancel : f.derivative.eval z * (-z1) = -f.eval z := by
    rw [hz1def]
    field_simp
  have heval : f.eval (z - z1) = q * z1 ^ 2 := by
    rw [show z - z1 = z + (-z1) by ring, hq, hcancel]
    ring
  have hevalnorm : ‖f.eval (z - z1)‖ ≤
      ‖f.derivative.eval a‖ ^ 2 * T f a ^ 2 ^ (n + 1) := by
    rw [heval, norm_mul, norm_pow]
    have hpow : (T f a ^ 2 ^ n) ^ 2 = T f a ^ 2 ^ (n + 1) := by
      rw [← pow_mul, pow_succ]
    have hstep : ‖f.eval z‖ / ‖f.derivative.eval a‖ ≤
        (‖f.derivative.eval a‖ ^ 2 * T f a ^ 2 ^ n) / ‖f.derivative.eval a‖ :=
      div_le_div_of_nonneg_right hz.2.1 hRpos.le
    have h0 : 0 ≤ ‖f.eval z‖ / ‖f.derivative.eval a‖ :=
      div_nonneg (norm_nonneg _) hRpos.le
    have h0' : 0 ≤ (‖f.derivative.eval a‖ ^ 2 * T f a ^ 2 ^ n) /
        ‖f.derivative.eval a‖ :=
      div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (T_nonneg f a) _)) hRpos.le
    calc ‖q‖ * ‖z1‖ ^ 2
        ≤ 1 * ‖z1‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right hqle (sq_nonneg _)
      _ = (‖f.eval z‖ / ‖f.derivative.eval a‖) ^ 2 := by rw [hz1norm]; ring
      _ ≤ ((‖f.derivative.eval a‖ ^ 2 * T f a ^ 2 ^ n) /
            ‖f.derivative.eval a‖) ^ 2 :=
          pow_le_pow_left₀ h0 hstep 2
      _ = (‖f.derivative.eval a‖ * T f a ^ 2 ^ n) ^ 2 := by field_simp
      _ = ‖f.derivative.eval a‖ ^ 2 * T f a ^ 2 ^ (n + 1) := by
          rw [mul_pow, hpow]
  exact ⟨hderiv_eq, hevalnorm, hz'int⟩

theorem newtonSeq_ih (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) (n : Nat) :
    ih f a hnorm n (newtonSeq f a n) := by
  induction n with
  | zero => exact ih_0 f a hf hnorm ha
  | succ n ih =>
      rw [newtonSeq_succ]
      exact ih_newtonStep f a hf ha hnorm ih

theorem newtonSeq_deriv_norm (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) (n : Nat) :
    ‖f.derivative.eval (newtonSeq f a n)‖ = ‖f.derivative.eval a‖ :=
  (newtonSeq_ih f a hf ha hnorm n).1

theorem newtonSeq_norm_le (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) (n : Nat) :
    ‖f.eval (newtonSeq f a n)‖ ≤ ‖f.derivative.eval a‖ ^ 2 * T f a ^ 2 ^ n :=
  (newtonSeq_ih f a hf ha hnorm n).2.1

theorem newtonSeq_norm_eq (n : Nat) :
    ‖newtonSeq f a (n + 1) - newtonSeq f a n‖ =
      ‖f.eval (newtonSeq f a n)‖ / ‖f.derivative.eval (newtonSeq f a n)‖ := by
  rw [newtonSeq_succ, newtonStep_eq, sub_sub_cancel_left, norm_neg, norm_div]

theorem newtonSeq_succ_dist (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) (n : Nat) :
    ‖newtonSeq f a (n + 1) - newtonSeq f a n‖ ≤
      ‖f.derivative.eval a‖ * T f a ^ 2 ^ n := by
  have hRpos : 0 < ‖f.derivative.eval a‖ := deriv_norm_pos f a hnorm
  calc ‖newtonSeq f a (n + 1) - newtonSeq f a n‖
      = ‖f.eval (newtonSeq f a n)‖ / ‖f.derivative.eval (newtonSeq f a n)‖ :=
        newtonSeq_norm_eq f a n
    _ = ‖f.eval (newtonSeq f a n)‖ / ‖f.derivative.eval a‖ := by
        rw [newtonSeq_deriv_norm f a hf ha hnorm n]
    _ ≤ (‖f.derivative.eval a‖ ^ 2 * T f a ^ 2 ^ n) / ‖f.derivative.eval a‖ :=
        div_le_div_of_nonneg_right (newtonSeq_norm_le f a hf ha hnorm n) hRpos.le
    _ = ‖f.derivative.eval a‖ * T f a ^ 2 ^ n := by field_simp

theorem newtonSeq_dist_aux (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) (n : Nat) :
    ∀ k : Nat, ‖newtonSeq f a (n + k) - newtonSeq f a n‖ ≤
      ‖f.derivative.eval a‖ * T f a ^ 2 ^ n := by
  intro k
  induction k with
  | zero => simp [T_nonneg, mul_nonneg]
  | succ k ih =>
      have h2 : 2 ^ n ≤ 2 ^ (n + k) := by
        apply Nat.pow_le_pow_right (by norm_num)
        omega
      calc ‖newtonSeq f a (n + (k + 1)) - newtonSeq f a n‖
          = ‖newtonSeq f a (n + k + 1) - newtonSeq f a n‖ := by rw [add_assoc]
        _ = ‖newtonSeq f a (n + k + 1) - newtonSeq f a (n + k) +
              (newtonSeq f a (n + k) - newtonSeq f a n)‖ := by
            rw [sub_add_sub_cancel]
        _ ≤ max ‖newtonSeq f a (n + k + 1) - newtonSeq f a (n + k)‖
              ‖newtonSeq f a (n + k) - newtonSeq f a n‖ :=
            norm_add_le_max' _ _
        _ ≤ max (‖f.derivative.eval a‖ * T f a ^ 2 ^ (n + k))
              (‖f.derivative.eval a‖ * T f a ^ 2 ^ n) :=
            max_le_max (newtonSeq_succ_dist f a hf ha hnorm (n + k)) ih
        _ = ‖f.derivative.eval a‖ * T f a ^ 2 ^ n :=
            max_eq_right <|
              mul_le_mul_of_nonneg_left
                (pow_le_pow_of_le_one (T_nonneg f a) (T_lt_one f a hnorm).le h2)
                (norm_nonneg _)

theorem newtonSeq_dist (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) {n k : Nat} (hnk : n ≤ k) :
    ‖newtonSeq f a k - newtonSeq f a n‖ ≤
      ‖f.derivative.eval a‖ * T f a ^ 2 ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnk
  exact newtonSeq_dist_aux f a hf ha hnorm n m

theorem bound_tendsto (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) :
    Tendsto (fun n : Nat => ‖f.derivative.eval a‖ * T f a ^ 2 ^ n) atTop (nhds 0) := by
  rw [← mul_zero ‖f.derivative.eval a‖]
  refine Tendsto.mul tendsto_const_nhds ?_
  exact Tendsto.comp
    (tendsto_pow_atTop_nhds_zero_of_lt_one (T_nonneg f a) (T_lt_one f a hnorm))
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Nat) < 2))

theorem bound_sq_tendsto (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) :
    Tendsto (fun n : Nat => ‖f.derivative.eval a‖ ^ 2 * T f a ^ 2 ^ n) atTop (nhds 0) := by
  have h : Tendsto (fun n : Nat => ‖f.derivative.eval a‖ *
      (‖f.derivative.eval a‖ * T f a ^ 2 ^ n)) atTop (nhds 0) := by
    have h1 := (bound_tendsto f a hnorm).const_mul ‖f.derivative.eval a‖
    simpa only [mul_zero] using h1
  simpa only [sq, mul_assoc] using h

theorem newtonSeq_cauchy (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) :
    CauchySeq (newtonSeq f a) := by
  refine cauchySeq_of_le_tendsto_0' (fun n => ‖f.derivative.eval a‖ * T f a ^ 2 ^ n)
    (fun n m hnm => ?_) (bound_tendsto f a hnorm)
  rw [dist_eq_norm, norm_sub_rev]
  exact newtonSeq_dist f a hf ha hnorm hnm

/-- The limit of the Newton sequence. -/
noncomputable def soln (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) : L :=
  Classical.choose (cauchySeq_tendsto_of_complete (newtonSeq_cauchy f a hf ha hnorm))

theorem soln_tendsto (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) :
    Tendsto (newtonSeq f a) atTop (nhds (soln f a hf ha hnorm)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (newtonSeq_cauchy f a hf ha hnorm))

theorem newtonSeq_eval_tendsto_zero (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) :
    Tendsto (fun n => ‖f.eval (newtonSeq f a n)‖) atTop (nhds 0) :=
  squeeze_zero (fun _ => norm_nonneg _) (newtonSeq_norm_le f a hf ha hnorm)
    (bound_sq_tendsto f a hnorm)

theorem eval_soln (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) :
    f.eval (soln f a hf ha hnorm) = 0 := by
  have hcont : Tendsto (fun n => f.eval (newtonSeq f a n)) atTop
      (nhds (f.eval (soln f a hf ha hnorm))) :=
    (Polynomial.continuousAt (p := f) (a := soln f a hf ha hnorm)).tendsto.comp
      (soln_tendsto f a hf ha hnorm)
  have hzero : Tendsto (fun n => f.eval (newtonSeq f a n)) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 (newtonSeq_eval_tendsto_zero f a hf ha hnorm)
  exact tendsto_nhds_unique hcont hzero

theorem newtonSeq_one : newtonSeq f a 1 = a - f.eval a / f.derivative.eval a := by
  rw [show (1 : Nat) = 0 + 1 from rfl, newtonSeq_succ, newtonSeq_zero, newtonStep_eq]

theorem newtonSeq_dist_to_a_le (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) :
    ∀ n : Nat, 1 ≤ n → ‖newtonSeq f a n - a‖ ≤ ‖f.derivative.eval a‖ * T f a := by
  intro n
  induction n with
  | zero => omega
  | succ k ih =>
      intro _
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        have hCe : ‖f.derivative.eval a‖ * T f a = ‖f.eval a‖ / ‖f.derivative.eval a‖ := by
          rw [T]; field_simp
        rw [newtonSeq_one, sub_sub_cancel_left, norm_neg, norm_div, hCe]
      · have hbk : ‖newtonSeq f a k - a‖ ≤ ‖f.derivative.eval a‖ * T f a := ih (by omega)
        have hsucc : ‖newtonSeq f a (k + 1) - a‖ ≤
            max ‖newtonSeq f a (k + 1) - newtonSeq f a k‖ ‖newtonSeq f a k - a‖ := by
          have h := norm_add_le_max'
            (newtonSeq f a (k + 1) - newtonSeq f a k) (newtonSeq f a k - a)
          rw [show newtonSeq f a (k + 1) - newtonSeq f a k +
            (newtonSeq f a k - a) = newtonSeq f a (k + 1) - a by ring] at h
          exact h
        refine hsucc.trans (max_le ?_ hbk)
        refine (newtonSeq_succ_dist f a hf ha hnorm k).trans ?_
        have h2n : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        simpa using pow_le_pow_of_le_one (T_nonneg f a) (T_lt_one f a hnorm).le h2n

theorem soln_dist_to_a_lt (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) :
    ‖soln f a hf ha hnorm - a‖ < ‖f.derivative.eval a‖ := by
  have hRpos : 0 < ‖f.derivative.eval a‖ := deriv_norm_pos f a hnorm
  have hlim : Tendsto (fun n => ‖newtonSeq f a n - a‖) atTop
      (nhds ‖soln f a hf ha hnorm - a‖) :=
    (continuous_norm.tendsto _).comp
      ((soln_tendsto f a hf ha hnorm).sub tendsto_const_nhds)
  have hle : ‖soln f a hf ha hnorm - a‖ ≤ ‖f.derivative.eval a‖ * T f a :=
    le_of_tendsto hlim (eventually_atTop.2
      ⟨1, fun n hn => newtonSeq_dist_to_a_le f a hf ha hnorm n hn⟩)
  have hT : ‖f.derivative.eval a‖ * T f a < ‖f.derivative.eval a‖ := by
    nlinarith [T_lt_one f a hnorm, hRpos]
  linarith

theorem exists_root_close_aux (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) :
    ∃ b : L, f.eval b = 0 ∧ ‖b - a‖ < ‖f.derivative.eval a‖ := by
  classical
  by_cases h0 : f.eval a = 0
  · refine ⟨a, h0, ?_⟩
    simpa using deriv_norm_pos f a hnorm
  · exact ⟨soln f a hf ha hnorm, eval_soln f a hf ha hnorm,
      soln_dist_to_a_lt f a hf ha hnorm⟩

end Main

/-! ## Main statements -/

/-- **Hensel near-root existence (integral form).** -/
theorem exists_root_close_of_norm_lt [CompleteSpace L] (f : L[X]) (a : L)
    (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) :
    ∃ b : L, f.eval b = 0 ∧ ‖b - a‖ < ‖f.derivative.eval a‖ :=
  exists_root_close_aux f a hf ha hnorm

/-- **Hensel near-root uniqueness (integral form).**  Two roots in the open ball of
radius ‖f'(a)‖ coincide. -/
theorem eq_of_roots_close (f : L[X]) (a b1 b2 : L)
    (hf : ∀ n, ‖f.coeff n‖ ≤ 1) (ha : ‖a‖ ≤ 1)
    (hnorm : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2)
    (h1 : f.eval b1 = 0) (h2 : f.eval b2 = 0)
    (hb1 : ‖b1 - a‖ < ‖f.derivative.eval a‖)
    (hb2 : ‖b2 - a‖ < ‖f.derivative.eval a‖) : b1 = b2 :=
  eq_of_roots_close_aux f a hf ha hnorm h1 h2 hb1 hb2

#print axioms exists_root_close_of_norm_lt
#print axioms eq_of_roots_close
end LeanFormal.IUT.XiFPaper.Mzk1LpHenselNearRootActual