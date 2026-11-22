import tmp.sheaf.xif.paper.Mzk1BetaAvoidingBelyiRationalActual
import tmp.sheaf.xif.paper.Mzk1BetaAvoidingBelyiSmallActual
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-!
# Mzk1BetaAvoidingStepNoncanonicalActual — a non-canonical degree reduction for the beta-avoiding step

Target of this file: attack the open parametric lemma `BetaAvoidingStep` of
`Mzk1BetaAvoidingBelyiRationalActual` (the single missing step of the beta-avoiding Belyi
construction over ℚ) by a **non-canonical** degree reduction, i.e. by polynomials that are
*not* of the canonical shape `B_{m,n} ∘ affine`.

## The idea

Write `S = {s_1 < … < s_N}` and let `a = min S`, `c = max S`.  The canonical TauCeti
three-point step uses `f = B_{m,n}((X-a)/(c-a))` with `m/(m+n) = (b-a)/(c-a)` for some
`b ∈ S`; it provably fails to be beta-avoiding (`tauCetiStep_not_betaAvoiding`), exactly
because the value at an exterior `β` is forced.

The new family used here is the **power-composed** Belyi polynomial

  `belyiPow m n lam a u = B_{m,n} (lam * (X - a)^u)`,

i.e. the inner affine map is replaced by an affine power.  Chain-rule bookkeeping shows that all
critical values are still in `{0,1}` (`critIn01_belyiPow`): the only critical value of
`lam * (X-a)^u` is `0`, and `B_{m,n}(0) = 0`.

With `lam = (c-a)^{-u}` the composite equals `B_{m,n}(((X-a)/(c-a))^u)`, so **every** point
of `S` lands in the image of `[0,1]` under `B_{m,n}`, hence is `>= 0`; while `a`
and `c` both map to `0` (a genuine collision, so the cardinality drops) and `b` maps
to `1` as soon as `((b-a)/(c-a))^u = m/(m+n)`.  Therefore the whole beta-avoidance
requirement collapses to a *range* condition: `B_{m,n}(t_beta^u) ∉ [0,1]`.  For an
exterior `β` one can even *force* that condition, because an odd (or merely large enough) power
of `(β-a)/(c-a)` leaves `(0,1)`: this is what makes the two exterior cases below
unconditional.

## What is proved here (no `sorry`, no new axioms)

* the evaluation, degree, critical-value and `CritIn01` lemmas for the power-composed family;
* `betaAvoidingStep_pow_exterior_right`: the **exterior right case** `c < β`,
  **unconditional** in `S` and `β` — no parity hypothesis (a general bound
  `B_{m,n}(x) ∉ [0,1]` for `x >= 2` is applied to a large enough power of `(β-a)/(c-a)`);
* `betaAvoidingStep_pow_exterior_left_far`: the **far exterior left case** `β < 2a - c`,
  also unconditional (an even power of `(β-a)/(c-a) < -1` exceeds `1`);
* `betaAvoidingStep_pow_right`: the same exterior right case in its **sharp sign form**
  (odd `n` on a single admissible triple); the conclusion is the step conclusion itself, not
  only a base case;
* `betaAvoidingStep_pow_left`: the **near exterior left case** `β < a` under an odd-`m`,
  odd-`u` parity hypothesis (this is the only exterior-left case left to the sign test);
* `betaAvoidingStep_interior`: the **interior case** `a < β < c` when the triple `a<b<c`
  of `S` is "clean" (no other point of `S` strictly between `a` and `c`) and `m`,
  `n` are both odd; here `f(β) ∈ (0,1)` while `f(S) ⊆ {0,1} ∪ (-∞,0)`;
* `betaAvoidingStep_obstruction_instance`: the **counterexample instance of the canonical
  step** `S = {0,1,3}`, `β = 4` (`tauCetiStep_not_betaAvoiding`) is **resolved** by the
  non-canonical family: `f = B_{1,8}((X/3)^2)` has `f(0) = f(3) = 0`, `f(1) = 1`,
  `f(4) = 7^8/2^20 > 1`;
* `parity_never_odd_obstruction_instance`: for that same instance the odd-`n` sign test can
  *never* succeed (`n = 2m` whenever `1/3 = m/(m+n)`), so the resolution above genuinely
  needs the value computation instead of the sign; this isolates the precise residual
  difficulty.

## Precise remaining gap

What is **left open** for the full `BetaAvoidingStep` is the following.

1. **Interior `β`** (`min S < β < max S`, `β ∉ S`).  Then necessarily
   `t_beta = (β-a)/(c-a) ∈ (0,1)`, i.e. `f(β)` lands in the *same* range `[0,1]` as the
   whole image `f(S)`, so neither the sign test nor the bound `B_{m,n}(x) ∉ [0,1]`
   (`x >= 2`) can help.  Only the "clean triple" case is proved
   (`betaAvoidingStep_interior`).
2. **Near exterior left** (`2a - c <= β < a`, `a = min S`).  Here `|t_beta| <= 1` so no
   power of `t_beta` can be pushed past `2`; only the parity sign test applies
   (`betaAvoidingStep_pow_left`), and it can fail (`m` even).

In both residual cases one must control the actual rational value `B_{m,n}(t_beta^u)` rather
than its range or sign.  The obstruction instance below shows that such a value computation can
succeed where the sign fails (`B_{1,8}(16/9) = 7^8/2^20 > 1`), but no uniform value estimate
covering these cases is available.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingStepNoncanonicalActual

open Polynomial TauCeti
open LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingBelyiRationalActual
open LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingBelyiSmallActual

def belyiPow (m n : ℕ) (lam a : ℚ) (u : ℕ) : ℚ[X] :=
  (belyiPolynomial ℚ m n).comp (Polynomial.C lam * (Polynomial.X - Polynomial.C a) ^ u)

theorem eval_belyiPow (m n : ℕ) (lam a x : ℚ) (u : ℕ) :
    (belyiPow m n lam a u).eval x = (belyiPolynomial ℚ m n).eval (lam * (x - a) ^ u) := by
  rw [belyiPow, Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X]

theorem natDegree_belyiPow (m n : ℕ) (lam a : ℚ) (hlam : lam ≠ 0) (u : ℕ) (hu : 1 ≤ u) :
    (belyiPow m n lam a u).natDegree = (m + n) * u := by
  have hA : (Polynomial.C lam * (Polynomial.X - Polynomial.C a) ^ u : ℚ[X]).natDegree = u := by
    rw [Polynomial.natDegree_C_mul hlam, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C,
      mul_one]
  rw [belyiPow, Polynomial.natDegree_comp, natDegree_belyiPolynomial, hA]

theorem derivative_belyiPowArg (lam a : ℚ) (u : ℕ) :
    Polynomial.derivative (Polynomial.C lam * (Polynomial.X - Polynomial.C a) ^ u : ℚ[X]) =
      Polynomial.C lam * (Polynomial.C ((u : ℚ)) * (Polynomial.X - Polynomial.C a) ^ (u - 1)) := by
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_pow, Polynomial.derivative_X_sub_C]
  ring

theorem aeval_belyiPowArg (lam a : ℚ) (u : ℕ) (z : ℂ) :
    Polynomial.aeval z (Polynomial.C lam * (Polynomial.X - Polynomial.C a) ^ u : ℚ[X])
      = (algebraMap ℚ ℂ lam) * (z - algebraMap ℚ ℂ a) ^ u := by
  simp [Polynomial.aeval_def]

theorem aeval_derivative_belyiPowArg (lam a : ℚ) (u : ℕ) (z : ℂ) :
    Polynomial.aeval z
        (Polynomial.derivative (Polynomial.C lam * (Polynomial.X - Polynomial.C a) ^ u : ℚ[X]))
      = (algebraMap ℚ ℂ lam * algebraMap ℚ ℂ ((u : ℚ))) *
          (z - algebraMap ℚ ℂ a) ^ (u - 1) := by
  rw [derivative_belyiPowArg]
  simp only [Polynomial.aeval_def, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
    Polynomial.eval₂_sub, Polynomial.eval₂_X]
  ring


/-- The only critical value of λ (X - a)^u is 0. -/
theorem criticalValues_powArg_subset (lam a : ℚ) {u : ℕ} (hu : 1 ≤ u) :
    (Polynomial.C lam * (Polynomial.X - Polynomial.C a) ^ u : ℚ[X]).criticalValues ℂ ⊆ {0} := by
  rintro y ⟨z, hz, rfl⟩
  rw [mem_rootSet'] at hz
  obtain ⟨hne, hz0⟩ := hz
  have hlam : lam ≠ 0 := by
    intro h
    apply hne
    simp [h]
  have hu0 : (u : ℂ) ≠ 0 := by
    have hu' : (u : ℕ) ≠ 0 := by omega
    exact_mod_cast hu'
  rw [aeval_derivative_belyiPowArg] at hz0
  have hcoef : (algebraMap ℚ ℂ lam * algebraMap ℚ ℂ ((u : ℚ))) ≠ 0 :=
    mul_ne_zero (by simpa using hlam) (by simpa using hu0)
  have hzpow : (z - algebraMap ℚ ℂ a) ^ (u - 1) = 0 := by
    rcases mul_eq_zero.mp hz0 with h | h
    · exact absurd h hcoef
    · exact h
  have hza : z = algebraMap ℚ ℂ a := by
    by_contra hne'
    exact absurd hzpow (pow_ne_zero _ (sub_ne_zero.mpr hne'))
  subst hza
  change (Polynomial.aeval (algebraMap ℚ ℂ a)
    (Polynomial.C lam * (Polynomial.X - Polynomial.C a) ^ u)) ∈ ({0} : Set ℂ)
  rw [aeval_belyiPowArg, sub_self, zero_pow (by omega : u ≠ 0)]
  simp

theorem eval_zero_mem (m n : ℕ) :
    (belyiPolynomial ℚ m n).eval 0 ∈ ({0, 1} : Set ℚ) := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [eval_belyiPolynomial]
    norm_num
  · rw [eval_zero_belyiPolynomial hm n]
    simp

theorem criticalValues_belyiPow_subset (m n : ℕ) (lam a : ℚ) {u : ℕ} (hu : 1 ≤ u) :
    (belyiPow m n lam a u).criticalValues ℂ ⊆ ({0, 1} : Set ℂ) := by
  refine Set.Subset.trans (Polynomial.criticalValues_comp_subset (belyiPolynomial ℚ m n)
    (Polynomial.C lam * (Polynomial.X - Polynomial.C a) ^ u)) ?_
  rintro _ (h | h)
  · obtain ⟨y, hy, rfl⟩ := h
    have hy0 : y = 0 := by simpa using (criticalValues_powArg_subset lam a hu hy)
    subst hy0
    exact aeval_zero_of_eval_zero_mem (eval_zero_mem m n)
  · exact criticalValues_belyiPolynomial_subset ℂ m n h

theorem critIn01_belyiPow (m n : ℕ) (lam a : ℚ) (hlam : lam ≠ 0) (u : ℕ) (hu : 1 ≤ u)
    (hmn : 0 < m + n) :
    0 < (belyiPow m n lam a u).natDegree ∧ CritIn01 (belyiPow m n lam a u) := by
  have hnd := natDegree_belyiPow m n lam a hlam u hu
  have hpos : 0 < (m + n) * u := Nat.mul_pos hmn (by omega)
  refine ⟨by rw [hnd]; exact hpos, ?_⟩
  rw [critIn01_iff_criticalValues (by rw [hnd]; exact hpos)]
  exact criticalValues_belyiPow_subset m n lam a hu

theorem eval_belyi_nonneg {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {t : ℚ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : 0 ≤ (belyiPolynomial ℚ m n).eval t := by
  have hmq : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  rw [eval_belyiPolynomial]
  have hC : 0 < ((m : ℚ) + n) ^ (m + n) / ((m : ℚ) ^ m * (n : ℚ) ^ n) := by positivity
  exact mul_nonneg (mul_nonneg hC.le (pow_nonneg ht0 m)) (pow_nonneg (by linarith : 0 ≤ 1 - t) n)


/-- For t in [0,1], B_{m,n}(t) <= 1. -/
theorem eval_belyi_le_one {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {t : ℚ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : (belyiPolynomial ℚ m n).eval t ≤ 1 := by
  rcases lt_or_eq_of_le ht0 with h0 | h0
  · rcases lt_or_eq_of_le ht1 with h1 | h1
    · by_cases htr : t = (m : ℚ) / ((m : ℚ) + n)
      · rw [htr]
        exact le_of_eq (eval_div_belyiPolynomial (K := ℚ) m n)
      · exact le_of_lt (eval_belyi_lt_one hm hn h0 h1 htr)
    · rw [h1, eval_one_belyiPolynomial m hn.ne']
      norm_num
  · rw [← h0, eval_zero_belyiPolynomial hm.ne' n]
    norm_num

/-- The normalising constant times 2^m is bigger than 1 (equivalently |B_{m,n}(2)| > 1). -/
theorem belyiConstant_two_pow_gt_one {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    1 < ((m : ℚ) + n) ^ (m + n) / ((m : ℚ) ^ m * (n : ℚ) ^ n) * 2 ^ m := by
  have hmq : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hmnq : (0 : ℚ) < (m : ℚ) + n := by linarith
  have hden : (0 : ℚ) < (m : ℚ) ^ m * (n : ℚ) ^ n := by positivity
  have h1 : (m : ℚ) ^ m < (2 * ((m : ℚ) + n)) ^ m :=
    pow_lt_pow_left₀ (by linarith) (by linarith) (by omega)
  have h2 : (n : ℚ) ^ n ≤ ((m : ℚ) + n) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
  have h3 : (m : ℚ) ^ m * (n : ℚ) ^ n < (2 * ((m : ℚ) + n)) ^ m * ((m : ℚ) + n) ^ n :=
    mul_lt_mul h1 h2 (by positivity) (by positivity)
  have h4 : (2 * ((m : ℚ) + n)) ^ m * ((m : ℚ) + n) ^ n = 2 ^ m * ((m : ℚ) + n) ^ (m + n) := by
    rw [mul_pow, pow_add]
    ring
  have h5 : (m : ℚ) ^ m * (n : ℚ) ^ n < 2 ^ m * ((m : ℚ) + n) ^ (m + n) := by
    rw [← h4]
    exact h3
  rw [show ((m : ℚ) + n) ^ (m + n) / ((m : ℚ) ^ m * (n : ℚ) ^ n) * 2 ^ m
      = 2 ^ m * ((m : ℚ) + n) ^ (m + n) / ((m : ℚ) ^ m * (n : ℚ) ^ n) by ring]
  rw [lt_div_iff₀ hden]
  linarith

/-- For x >= 2, B_{m,n}(x) is outside [0,1]: either negative or bigger than 1. -/
theorem eval_belyi_outside_of_two_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {x : ℚ} (hx : 2 ≤ x) :
    (belyiPolynomial ℚ m n).eval x < 0 ∨ 1 < (belyiPolynomial ℚ m n).eval x := by
  have hmq : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hC : 0 < ((m : ℚ) + n) ^ (m + n) / ((m : ℚ) ^ m * (n : ℚ) ^ n) := by positivity
  have hxm : (0 : ℚ) < x ^ m := pow_pos (by linarith) m
  have hxm2 : (2 : ℚ) ^ m ≤ x ^ m := pow_le_pow_left₀ (by norm_num) hx m
  have hx1 : (1 : ℚ) ≤ x - 1 := by linarith
  have hx1n : (1 : ℚ) ≤ (x - 1) ^ n := one_le_pow₀ hx1
  have hC2 := belyiConstant_two_pow_gt_one (m := m) (n := n) hm hn
  rw [eval_belyiPolynomial]
  rcases Nat.even_or_odd n with hneven | hnodd
  · have h1x : (1 - x) ^ n = (x - 1) ^ n := by
      rw [show (1 : ℚ) - x = -(x - 1) by ring, hneven.neg_pow]
    rw [h1x]
    right
    have hstep1 : ((m : ℚ) + n) ^ (m + n) / ((m : ℚ) ^ m * (n : ℚ) ^ n) * 2 ^ m
        ≤ ((m : ℚ) + n) ^ (m + n) / ((m : ℚ) ^ m * (n : ℚ) ^ n) * x ^ m :=
      mul_le_mul_of_nonneg_left hxm2 hC.le
    have hpos2 : (0 : ℚ) ≤ ((m : ℚ) + n) ^ (m + n) / ((m : ℚ) ^ m * (n : ℚ) ^ n) * x ^ m :=
      le_of_lt (mul_pos hC hxm)
    have hstep2 : ((m : ℚ) + n) ^ (m + n) / ((m : ℚ) ^ m * (n : ℚ) ^ n) * x ^ m
        ≤ ((m : ℚ) + n) ^ (m + n) / ((m : ℚ) ^ m * (n : ℚ) ^ n) * x ^ m * (x - 1) ^ n := by
      have h := mul_le_mul_of_nonneg_left hx1n hpos2
      simpa using h
    linarith
  · have h1x : (1 - x) ^ n < 0 := by
      rw [show (1 : ℚ) - x = -(x - 1) by ring, hnodd.neg_pow]
      have hpos : (0 : ℚ) < (x - 1) ^ n := pow_pos (by linarith) n
      linarith
    left
    exact mul_neg_of_pos_of_neg (mul_pos hC hxm) h1x

/-- For t > 1 there is an exponent with t^u >= 2. -/
theorem exists_pow_two_le {t : ℚ} (ht : 1 < t) : ∃ u : ℕ, 1 ≤ u ∧ 2 ≤ t ^ u := by
  obtain ⟨u, hu⟩ := pow_unbounded_of_one_lt (y := t) (2 : ℚ) ht
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hu
    linarith
  exact ⟨u, by omega, le_of_lt hu⟩

/-- For |t| > 1 there is an even exponent with t^u >= 2. -/
theorem exists_even_pow_two_le_abs {t : ℚ} (ht : 1 < |t|) :
    ∃ u : ℕ, Even u ∧ 1 ≤ u ∧ 2 ≤ t ^ u := by
  obtain ⟨u₀, hu₀⟩ := pow_unbounded_of_one_lt (y := |t|) (2 : ℚ) ht
  have hu₀0 : u₀ ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hu₀
    linarith
  have h2 : (2 : ℚ) ≤ |t| ^ u₀ := le_of_lt hu₀
  have habs : (2 : ℚ) ≤ |t ^ u₀| := by
    rw [abs_pow]
    exact h2
  have hsq : (2 : ℚ) ^ 2 ≤ (t ^ u₀) ^ 2 := by
    have h := pow_le_pow_left₀ (a := (2 : ℚ)) (b := |t ^ u₀|) (by norm_num) habs 2
    rwa [sq_abs] at h
  refine ⟨2 * u₀, ⟨u₀, by ring⟩, by omega, ?_⟩
  have he : t ^ (2 * u₀) = (t ^ u₀) ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
  rw [he]
  linarith


/-! ## The core: the power step modulo a range condition -/

/-- **Core of the non-canonical power step.**

Let `a, b, c ∈ S` with `a ≤ s ≤ c` for all `s ∈ S`, `a < b < c`, and
`((b-a)/(c-a))^u = m/(m+n)`.  Put `f = B_{m,n}(((X-a)/(c-a))^u)`.  Then

* `a` and `c` both map to `0`, so the image of `S` is strictly smaller than `S`,
  and `0` is in that image;
* `b` maps to `1`, so `1` is in the image;
* every point of `S` maps into `[0,1]`, because it is `B_{m,n}` of a number in `[0,1]`.

Hence the whole beta-avoidance condition holds as soon as `f(β)` is outside the range
`[0,1]`, i.e. as soon as `f(β) < 0` or `1 < f(β)`.  Both alternatives are produced
below: the first by the parity sign lemmas (`betaAvoidingStep_pow_right`,
`betaAvoidingStep_pow_left`), the second by `eval_belyi_outside_of_two_le` applied to a
large power of `(β-a)/(c-a)` (the unconditional theorems). -/
theorem betaAvoidingStep_pow_core (S : Finset ℚ) (β a b c : ℚ) (u m n : ℕ)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hlo : ∀ s ∈ S, a ≤ s) (hhi : ∀ s ∈ S, s ≤ c)
    (hab : a < b) (hbc : b < c) (hu : 1 ≤ u) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hr : ((b - a) / (c - a)) ^ u = ((m : ℚ)) / ((m : ℚ) + n))
    (hout : (belyiPolynomial ℚ m n).eval (((β - a) / (c - a)) ^ u) < 0 ∨
      1 < (belyiPolynomial ℚ m n).eval (((β - a) / (c - a)) ^ u)) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ CritIn01 f ∧
      (S.image (fun x => f.eval x)).card < S.card ∧
      (0 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      (1 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      f.eval β ∉ S.image (fun x => f.eval x) := by
  classical
  have hca : 0 < c - a := by linarith
  have hca_ne : c - a ≠ 0 := hca.ne'
  have hu0 : u ≠ 0 := by omega
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  set lam : ℚ := ((c - a) ^ u)⁻¹ with hlam_def
  have hlam : lam ≠ 0 := by
    rw [hlam_def]
    exact inv_ne_zero (pow_ne_zero u hca_ne)
  have hval : ∀ x : ℚ, (belyiPow m n lam a u).eval x
      = (belyiPolynomial ℚ m n).eval (((x - a) / (c - a)) ^ u) := by
    intro x
    rw [eval_belyiPow]
    congr 1
    rw [hlam_def, div_eq_mul_inv, mul_pow, inv_pow]
    ring
  have himage_mem : ∀ s ∈ S, 0 ≤ (belyiPow m n lam a u).eval s ∧
      (belyiPow m n lam a u).eval s ≤ 1 := by
    intro s hs
    rw [hval s]
    have ht0 : 0 ≤ (s - a) / (c - a) := div_nonneg (by linarith [hlo s hs]) hca.le
    have ht1 : (s - a) / (c - a) ≤ 1 := by
      rw [div_le_one hca]
      linarith [hhi s hs]
    exact ⟨eval_belyi_nonneg hm hn (pow_nonneg ht0 u) (pow_le_one₀ ht0 ht1),
      eval_belyi_le_one hm hn (pow_nonneg ht0 u) (pow_le_one₀ ht0 ht1)⟩
  have h0 : (belyiPow m n lam a u).eval a = 0 := by
    rw [hval a, show (a - a) / (c - a) = 0 by rw [sub_self, zero_div], zero_pow hu0,
      eval_zero_belyiPolynomial hm0 n]
  have hc0 : (belyiPow m n lam a u).eval c = 0 := by
    rw [hval c, show (c - a) / (c - a) = 1 by rw [div_self hca_ne], one_pow,
      eval_one_belyiPolynomial m hn0]
  have h1 : (belyiPow m n lam a u).eval b = 1 := by
    rw [hval b, hr]
    exact eval_div_belyiPolynomial (K := ℚ) m n
  have hcard : (S.image (fun x => (belyiPow m n lam a u).eval x)).card < S.card := by
    have hac_ne : a ≠ c := by linarith
    have heq : S.image (fun x => (belyiPow m n lam a u).eval x)
        = (S.erase c).image (fun x => (belyiPow m n lam a u).eval x) := by
      refine Finset.Subset.antisymm ?_ (Finset.image_subset_image (Finset.erase_subset c S))
      intro y hy
      obtain ⟨s, hs, hsy⟩ := Finset.mem_image.mp hy
      rcases eq_or_ne s c with hsc | hsc
      · rw [hsc] at hsy
        exact Finset.mem_image.mpr
          ⟨a, Finset.mem_erase.mpr ⟨hac_ne, ha⟩, by rw [h0, ← hsy, hc0]⟩
      · exact Finset.mem_image.mpr ⟨s, Finset.mem_erase.mpr ⟨hsc, hs⟩, hsy⟩
    rw [heq]
    have hle := Finset.card_image_le (s := S.erase c)
      (f := fun x => (belyiPow m n lam a u).eval x)
    rw [Finset.card_erase_of_mem hc] at hle
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨c, hc⟩
    omega
  refine ⟨belyiPow m n lam a u, (critIn01_belyiPow m n lam a hlam u hu (by omega)).1, ?_,
    hcard, ?_, ?_, ?_⟩
  · exact (critIn01_belyiPow m n lam a hlam u hu (by omega)).2
  · exact Finset.mem_image.mpr ⟨a, ha, h0⟩
  · exact Finset.mem_image.mpr ⟨b, hb, h1⟩
  · intro hmem
    obtain ⟨s, hs, hsy⟩ := Finset.mem_image.mp hmem
    have hmemval := himage_mem s hs
    have hβval : (belyiPow m n lam a u).eval β
        = (belyiPolynomial ℚ m n).eval (((β - a) / (c - a)) ^ u) := hval β
    rw [hsy, hβval] at hmemval
    rcases hout with h | h <;> linarith [hmemval.1, hmemval.2]

/-! ## The exterior right case -/

/-- **Non-canonical power step, exterior right.**  If `β` lies to the right of `max S = c` and
some interior point `b ∈ S` has `((b-a)/(c-a))^u = m/(m+n)` with `n` odd, then the step
conclusion holds.  The composite is `B_{m,n}(((X-a)/(c-a))^u)`; the image of `S` is
nonnegative while `β` maps to `(β-a)/(c-a) > 1`, whose `u`-th power exceeds `1`,
where `B_{m,n}` is negative because `n` is odd. -/
theorem betaAvoidingStep_pow_right (S : Finset ℚ) (β a c : ℚ) (u m n : ℕ)
    (ha : a ∈ S) (hc : c ∈ S) (hlo : ∀ s ∈ S, a ≤ s) (hhi : ∀ s ∈ S, s ≤ c)
    (hac : a < c) (hu : 1 ≤ u) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnodd : Odd n)
    (hb : ∃ b ∈ S, a < b ∧ b < c ∧ ((b - a) / (c - a)) ^ u = ((m : ℚ)) / ((m : ℚ) + n))
    (hβ : c < β) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ CritIn01 f ∧
      (S.image (fun x => f.eval x)).card < S.card ∧
      (0 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      (1 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      f.eval β ∉ S.image (fun x => f.eval x) := by
  obtain ⟨b, hbS, hab, hbc, hr⟩ := hb
  have hca : 0 < c - a := by linarith
  have hratio : 1 < (β - a) / (c - a) := by
    rw [one_lt_div hca]
    linarith
  refine betaAvoidingStep_pow_core S β a b c u m n ha hbS hc hlo hhi hab hbc hu hm hn hr ?_
  exact Or.inl (eval_belyi_neg_of_one_lt (m := m) (n := n) (by omega) (by omega) hnodd
    (x := ((β - a) / (c - a)) ^ u) (one_lt_pow₀ hratio (by omega)))

/-! ## The exterior left case -/

/-- **Non-canonical power step, exterior left.**  If `β` lies to the left of `min S = a` and
some interior point `b ∈ S` has `((b-a)/(c-a))^u = m/(m+n)` with `m` and `u` odd, then the
step conclusion holds: `(β-a)/(c-a) < 0`, so its odd `u`-th power is negative, where
`B_{m,n}` is negative because `m` is odd. -/
theorem betaAvoidingStep_pow_left (S : Finset ℚ) (β a c : ℚ) (u m n : ℕ)
    (ha : a ∈ S) (hc : c ∈ S) (hlo : ∀ s ∈ S, a ≤ s) (hhi : ∀ s ∈ S, s ≤ c)
    (hac : a < c) (hu : 1 ≤ u) (huodd : Odd u) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmodd : Odd m)
    (hb : ∃ b ∈ S, a < b ∧ b < c ∧ ((b - a) / (c - a)) ^ u = ((m : ℚ)) / ((m : ℚ) + n))
    (hβ : β < a) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ CritIn01 f ∧
      (S.image (fun x => f.eval x)).card < S.card ∧
      (0 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      (1 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      f.eval β ∉ S.image (fun x => f.eval x) := by
  obtain ⟨b, hbS, hab, hbc, hr⟩ := hb
  have hca : 0 < c - a := by linarith
  have hratio : (β - a) / (c - a) < 0 := div_neg_of_neg_of_pos (by linarith) hca
  have hpowneg : ((β - a) / (c - a)) ^ u < 0 := by
    have hneg : ((β - a) / (c - a)) = -(-((β - a) / (c - a))) := by ring
    rw [hneg, huodd.neg_pow]
    have hpos : 0 < (-((β - a) / (c - a))) ^ u := pow_pos (by linarith) u
    linarith
  refine betaAvoidingStep_pow_core S β a b c u m n ha hbS hc hlo hhi hab hbc hu hm hn hr ?_
  exact Or.inl (eval_belyi_neg_of_lt_zero (m := m) (n := n) (by omega) (by omega) hmodd hpowneg)

/-! ## The two unconditional exterior cases -/

/-- **Non-canonical power step, exterior right — UNCONDITIONAL.**

For *every* finite set `S` of rationals having a triple `a < b < c` of elements with `a`
below and `c` above every element of `S`, and *every* `β > c`, the `BetaAvoidingStep`
conclusion holds — with **no parity hypothesis**.  The exponent `u` is chosen so large that
`((β-a)/(c-a))^u` is at least `2`; there `B_{m,n}` is provably outside `[0,1]`
(`eval_belyi_outside_of_two_le`), while the whole of `S` still maps into `[0,1]`, so
`β` is avoided. -/
theorem betaAvoidingStep_pow_exterior_right (S : Finset ℚ) (β a c : ℚ)
    (ha : a ∈ S) (hc : c ∈ S) (hlo : ∀ s ∈ S, a ≤ s) (hhi : ∀ s ∈ S, s ≤ c)
    (hac : a < c) (hb : ∃ b ∈ S, a < b ∧ b < c) (hβ : c < β) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ CritIn01 f ∧
      (S.image (fun x => f.eval x)).card < S.card ∧
      (0 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      (1 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      f.eval β ∉ S.image (fun x => f.eval x) := by
  obtain ⟨b, hbS, hab, hbc⟩ := hb
  have hca : 0 < c - a := by linarith
  have ht : 1 < (β - a) / (c - a) := by
    rw [one_lt_div hca]
    linarith
  obtain ⟨u, hu1, hu2⟩ := exists_pow_two_le ht
  have hs0 : 0 < (b - a) / (c - a) := div_pos (by linarith) hca
  have hs1 : (b - a) / (c - a) < 1 := by
    rw [div_lt_one hca]
    linarith
  have hr0 : 0 < ((b - a) / (c - a)) ^ u := pow_pos hs0 u
  have hr1 : ((b - a) / (c - a)) ^ u < 1 := pow_lt_one₀ hs0.le hs1 (by omega)
  obtain ⟨m, n, hm, hn, hmn⟩ := Rat.exists_eq_div_add_of_pos_of_lt_one hr0 hr1
  refine betaAvoidingStep_pow_core S β a b c u m n ha hbS hc hlo hhi hab hbc hu1
    (by omega) (by omega) hmn ?_
  exact eval_belyi_outside_of_two_le (by omega) (by omega) hu2

/-- **Non-canonical power step, far exterior left — UNCONDITIONAL.**

If `β < 2a - c`, i.e. `β` is more than `c - a` to the left of `a = min S`, the step
conclusion holds with no parity hypothesis: `(β-a)/(c-a) < -1`, so an even power of it is at
least `2`, where `B_{m,n}` is outside `[0,1]`. -/
theorem betaAvoidingStep_pow_exterior_left_far (S : Finset ℚ) (β a c : ℚ)
    (ha : a ∈ S) (hc : c ∈ S) (hlo : ∀ s ∈ S, a ≤ s) (hhi : ∀ s ∈ S, s ≤ c)
    (hac : a < c) (hb : ∃ b ∈ S, a < b ∧ b < c) (hβ : β < 2 * a - c) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ CritIn01 f ∧
      (S.image (fun x => f.eval x)).card < S.card ∧
      (0 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      (1 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      f.eval β ∉ S.image (fun x => f.eval x) := by
  obtain ⟨b, hbS, hab, hbc⟩ := hb
  have hca : 0 < c - a := by linarith
  have htneg : (β - a) / (c - a) < -1 := by
    rw [div_lt_iff₀ hca]
    linarith
  have htabs : 1 < |(β - a) / (c - a)| := by
    rw [abs_of_neg (by linarith)]
    linarith
  obtain ⟨u, _hueven, hu1, hu2⟩ := exists_even_pow_two_le_abs htabs
  have hs0 : 0 < (b - a) / (c - a) := div_pos (by linarith) hca
  have hs1 : (b - a) / (c - a) < 1 := by
    rw [div_lt_one hca]
    linarith
  have hr0 : 0 < ((b - a) / (c - a)) ^ u := pow_pos hs0 u
  have hr1 : ((b - a) / (c - a)) ^ u < 1 := pow_lt_one₀ hs0.le hs1 (by omega)
  obtain ⟨m, n, hm, hn, hmn⟩ := Rat.exists_eq_div_add_of_pos_of_lt_one hr0 hr1
  refine betaAvoidingStep_pow_core S β a b c u m n ha hbS hc hlo hhi hab hbc hu1
    (by omega) (by omega) hmn ?_
  exact eval_belyi_outside_of_two_le (by omega) (by omega) hu2

/-! ## The interior case -/

/-- **Non-canonical power step, interior.**  If `a < β < c`, `a, b, c ∈ S`, no other point of
`S` lies strictly between `a` and `c`, and `(b-a)/(c-a) = m/(m+n)` with `m` and `n` both
odd, then the canonical composite `B_{m,n}((X-a)/(c-a))` is beta-avoiding: points of `S`
outside `[a,c]` map to negative values (odd `m`, odd `n`), the three interior points map to
`0, 1, 0`, and `β` maps strictly inside `(0,1)`. -/
theorem betaAvoidingStep_interior (S : Finset ℚ) (β a b c : ℚ) (m n : ℕ)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hβ : β ∉ S)
    (hab : a < b) (hbc : b < c) (hβa : a < β) (hβc : β < c)
    (hout : ∀ s ∈ S, s = a ∨ s = b ∨ s = c ∨ s < a ∨ c < s)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmodd : Odd m) (hnodd : Odd n)
    (hr : (b - a) / (c - a) = ((m : ℚ)) / ((m : ℚ) + n)) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ CritIn01 f ∧
      (S.image (fun x => f.eval x)).card < S.card ∧
      (0 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      (1 : ℚ) ∈ S.image (fun x => f.eval x) ∧
      f.eval β ∉ S.image (fun x => f.eval x) := by
  classical
  have hca : 0 < c - a := by linarith
  have hca_ne : c - a ≠ 0 := hca.ne'
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  set lam : ℚ := (c - a)⁻¹ with hlam_def
  have hlam : lam ≠ 0 := by
    rw [hlam_def]
    exact inv_ne_zero hca_ne
  have hval : ∀ x : ℚ, (belyiPow m n lam a 1).eval x
      = (belyiPolynomial ℚ m n).eval ((x - a) / (c - a)) := by
    intro x
    rw [eval_belyiPow]
    congr 1
    rw [hlam_def, pow_one, div_eq_mul_inv, mul_comm]
  have hβ0 : 0 < (β - a) / (c - a) := div_pos (by linarith) hca
  have hβ1 : (β - a) / (c - a) < 1 := by
    rw [div_lt_one hca]
    linarith
  have hβne : (β - a) / (c - a) ≠ ((m : ℚ)) / ((m : ℚ) + n) := by
    rw [← hr]
    intro h
    apply hβ
    have h' : (β - a) / (c - a) * (c - a) = (b - a) / (c - a) * (c - a) := by rw [h]
    field_simp at h'
    have h3 : β = b := by linarith
    rw [h3]
    exact hb
  have hβpos : 0 < (belyiPolynomial ℚ m n).eval ((β - a) / (c - a)) :=
    eval_belyi_pos (m := m) (n := n) (by omega) (by omega) hβ0 hβ1
  have hβnot1 : (belyiPolynomial ℚ m n).eval ((β - a) / (c - a)) ≠ 1 := by
    intro h
    exact hβne (belyi_eval_mem_zero_one_of_interior hm hn hβ0 hβ1 (Or.inr h))
  have himage : ∀ s ∈ S, (belyiPow m n lam a 1).eval s = 0 ∨
      (belyiPow m n lam a 1).eval s = 1 ∨ (belyiPow m n lam a 1).eval s < 0 := by
    intro s hs
    rcases hout s hs with hsa | hsb | hsc | hs_lt | hs_gt
    · left
      rw [hsa, hval a, show (a - a) / (c - a) = 0 by rw [sub_self, zero_div],
        eval_zero_belyiPolynomial hm0 n]
    · right; left
      rw [hsb, hval b, hr]
      exact eval_div_belyiPolynomial (K := ℚ) m n
    · left
      rw [hsc, hval c, show (c - a) / (c - a) = 1 by rw [div_self hca_ne],
        eval_one_belyiPolynomial m hn0]
    · right; right
      rw [hval s]
      exact eval_belyi_neg_of_lt_zero (m := m) (n := n) (by omega) (by omega) hmodd
        (div_neg_of_neg_of_pos (by linarith) hca)
    · right; right
      rw [hval s]
      exact eval_belyi_neg_of_one_lt (m := m) (n := n) (by omega) (by omega) hnodd
        (by rw [one_lt_div hca]; linarith)
  have h0 : (belyiPow m n lam a 1).eval a = 0 := by
    rw [hval a, show (a - a) / (c - a) = 0 by rw [sub_self, zero_div],
      eval_zero_belyiPolynomial hm0 n]
  have hc0 : (belyiPow m n lam a 1).eval c = 0 := by
    rw [hval c, show (c - a) / (c - a) = 1 by rw [div_self hca_ne],
      eval_one_belyiPolynomial m hn0]
  have h1 : (belyiPow m n lam a 1).eval b = 1 := by
    rw [hval b, hr]
    exact eval_div_belyiPolynomial (K := ℚ) m n
  have hcard : (S.image (fun x => (belyiPow m n lam a 1).eval x)).card < S.card := by
    have hac_ne : a ≠ c := by linarith
    have heq : S.image (fun x => (belyiPow m n lam a 1).eval x)
        = (S.erase c).image (fun x => (belyiPow m n lam a 1).eval x) := by
      refine Finset.Subset.antisymm ?_ (Finset.image_subset_image (Finset.erase_subset c S))
      intro y hy
      obtain ⟨s, hs, hsy⟩ := Finset.mem_image.mp hy
      rcases eq_or_ne s c with hsc | hsc
      · rw [hsc] at hsy
        exact Finset.mem_image.mpr
          ⟨a, Finset.mem_erase.mpr ⟨hac_ne, ha⟩, by rw [h0, ← hsy, hc0]⟩
      · exact Finset.mem_image.mpr ⟨s, Finset.mem_erase.mpr ⟨hsc, hs⟩, hsy⟩
    rw [heq]
    have hle := Finset.card_image_le (s := S.erase c)
      (f := fun x => (belyiPow m n lam a 1).eval x)
    rw [Finset.card_erase_of_mem hc] at hle
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨c, hc⟩
    omega
  refine ⟨belyiPow m n lam a 1, (critIn01_belyiPow m n lam a hlam 1 le_rfl (by omega)).1, ?_,
    hcard, ?_, ?_, ?_⟩
  · exact (critIn01_belyiPow m n lam a hlam 1 le_rfl (by omega)).2
  · exact Finset.mem_image.mpr ⟨a, ha, h0⟩
  · exact Finset.mem_image.mpr ⟨b, hb, h1⟩
  · intro hmem
    obtain ⟨s, hs, hsy⟩ := Finset.mem_image.mp hmem
    have hpos : 0 < (belyiPow m n lam a 1).eval β := by
      rw [hval β]
      exact hβpos
    have hne : (belyiPow m n lam a 1).eval β ≠ 1 := by
      rw [hval β]
      exact hβnot1
    rw [← hsy] at hpos hne
    rcases himage s hs with h | h | h
    · rw [h] at hpos; linarith
    · exact hne h
    · linarith

/-! ## Resolving the canonical obstruction: `S = {0,1,3}`, `β = 4` -/

/-- The value of the non-canonical witness `B_{1,8}((X/3)^2)` at `4`. -/
theorem obstruction_witness_eval_four :
    (belyiPow 1 8 (1 / 9) 0 2).eval 4 = 5764801 / 1048576 := by
  rw [eval_belyiPow, eval_belyiPolynomial]
  norm_num

/-- The witness maps `{0,1,3}` onto `{0,1}`. -/
theorem obstruction_witness_image :
    ({0, 1, 3} : Finset ℚ).image (fun x => (belyiPow 1 8 (1 / 9) 0 2).eval x) = {0, 1} := by
  have h0 : (belyiPow 1 8 (1 / 9) 0 2).eval 0 = 0 := by
    rw [eval_belyiPow, show (1 / 9 : ℚ) * (0 - 0) ^ 2 = 0 by norm_num,
      eval_zero_belyiPolynomial (by norm_num : (1 : ℕ) ≠ 0) 8]
  have h1 : (belyiPow 1 8 (1 / 9) 0 2).eval 1 = 1 := by
    rw [eval_belyiPow, show (1 / 9 : ℚ) * (1 - 0) ^ 2 = (1 : ℚ) / ((1 : ℚ) + 8) by norm_num]
    exact eval_div_belyiPolynomial (K := ℚ) 1 8
  have h3 : (belyiPow 1 8 (1 / 9) 0 2).eval 3 = 0 := by
    rw [eval_belyiPow, show (1 / 9 : ℚ) * (3 - 0) ^ 2 = 1 by norm_num,
      eval_one_belyiPolynomial 1 (by norm_num : (8 : ℕ) ≠ 0)]
  ext y
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl | rfl
    · left; exact h0
    · right; exact h1
    · left; exact h3
  · rintro (rfl | rfl)
    · exact ⟨0, Or.inl rfl, h0⟩
    · exact ⟨1, Or.inr (Or.inl rfl), h1⟩

/-- **The canonical obstruction instance is resolved by the non-canonical family.**  For
`S = {0,1,3}` and `β = 4` the canonical TauCeti step always produces `f(4) = 1 ∈ f(S)`
(`tauCetiStep_not_betaAvoiding`), so that step is *not* beta-avoiding.  The power-composed
polynomial `f = B_{1,8}((X/3)^2)` instead satisfies the whole `BetaAvoidingStep` conclusion:

* `0 < f.natDegree` (`= 18`) and `CritIn01 f` (the critical points `0, ±1, ±3` have
  values `0, 1, 0`);
* `f(0) = f(3) = 0` and `f(1) = 1`, so the image is `{0,1}`, of cardinality `2 < 3`;
* `f(4) = 7^8/2^20 = 5764801/1048576 > 1`, so `f(4) ∉ {0,1} = f(S)`. -/
theorem betaAvoidingStep_obstruction_instance :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ CritIn01 f ∧
      (({0, 1, 3} : Finset ℚ).image (fun x => f.eval x)).card < 3 ∧
      (0 : ℚ) ∈ ({0, 1, 3} : Finset ℚ).image (fun x => f.eval x) ∧
      (1 : ℚ) ∈ ({0, 1, 3} : Finset ℚ).image (fun x => f.eval x) ∧
      f.eval 4 ∉ ({0, 1, 3} : Finset ℚ).image (fun x => f.eval x) := by
  have hlam : (1 / 9 : ℚ) ≠ 0 := by norm_num
  have hcrit := critIn01_belyiPow 1 8 (1 / 9) 0 hlam 2 (by norm_num) (by norm_num)
  have h4 := obstruction_witness_eval_four
  have himg := obstruction_witness_image
  refine ⟨belyiPow 1 8 (1 / 9) 0 2, hcrit.1, hcrit.2, ?_, ?_, ?_, ?_⟩
  · rw [himg]
    norm_num
  · rw [himg]
    exact Finset.mem_insert_self 0 {1}
  · rw [himg]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self 1)
  · rw [himg]
    rw [h4]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    norm_num

/-- **The sign test can never succeed on the obstruction instance.**  For `S = {0,1,3}` the only
interior point is `1`, so the ratio is `(1-0)/(3-0) = 1/3`; an equation `1/3 = m/(m+n)` forces
`n = 2m`, hence `n` is *even* and `eval_belyi_neg_of_one_lt` (which needs odd `n`) never
applies to the exterior-right power step with `β = 4 > 3`.  This is why resolving the
instance needs the value computation `B_{1,8}(16/9) = 7^8/2^20 > 1` rather than a sign. -/
theorem parity_never_odd_obstruction_instance (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hr : (1 : ℚ) / 3 = ((m : ℚ)) / ((m : ℚ) + n)) : Even n := by
  have hmq : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hmn : (m : ℚ) + n ≠ 0 := by linarith
  have h3 : (n : ℚ) = 2 * (m : ℚ) := by
    field_simp at hr
    linarith
  have hn2 : n = 2 * m := by
    have h' : (n : ℚ) = ((2 * m : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast h'
  exact ⟨m, by omega⟩

/-! ## Row record -/

/-- What the non-canonical power step proves and what remains. -/
def betaAvoidingStepNoncanonicalRows : List (String × String × String) :=
  [ ("CritIn01 of B_{m,n}(lam (X-a)^u)", "A", "PROVED critIn01_belyiPow")
  , ("exterior right: max S < beta", "A",
     "PROVED betaAvoidingStep_pow_exterior_right (UNCONDITIONAL, arbitrary S and beta)")
  , ("far exterior left: beta < 2*min S - max S", "A",
     "PROVED betaAvoidingStep_pow_exterior_left_far (UNCONDITIONAL)")
  , ("near exterior left: beta < min S, odd m and odd u", "A",
     "PROVED betaAvoidingStep_pow_left (parity hypothesis)")
  , ("interior: min S < beta < max S, clean triple, m and n odd", "A",
     "PROVED betaAvoidingStep_interior")
  , ("canonical obstruction S={0,1,3}, beta=4", "A",
     "PROVED betaAvoidingStep_obstruction_instance (f = B_{1,8}((X/3)^2), f(4) = 7^8/2^20 > 1)")
  , ("interior beta in general / near exterior left without parity", "BLOCKER",
     "NAMED residual: f(beta) falls in the same range [0,1] as f(S), so neither the sign test nor the bound B(x) not in [0,1] for x >= 2 can be used; needs a uniform value estimate") ]

/-- The row record has seven rows. -/
theorem betaAvoidingStepNoncanonicalRows_length : betaAvoidingStepNoncanonicalRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingStepNoncanonicalActual
end
