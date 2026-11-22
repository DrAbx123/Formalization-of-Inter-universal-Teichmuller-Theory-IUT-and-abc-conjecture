import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Task F kernel: finite-orbit normalization and root-of-unity log invariance

This file records only the two elementary facts that any equivariant/orbifold
log-volume for the mu_{2l} root stack must satisfy.  It does not construct the
paper root, does not define the paper Theta hull, and does not assert any
paper-level equality.  The exact paper gaps are recorded in the accompanying
memo TASK_F_EQUIVARIANT_ORBIFOLD_MEMO.md.

No sorry, no axiom, no fake object.
-/

noncomputable section
set_option linter.unusedVariables false
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.TaskFEquivariantOrbifoldKernel

/-! ## 1. Log of a root: the 1/(2l) normalization -/

/-- If r ^ n = q with q,r > 0, then log r = log q / n. -/
theorem log_eq_log_div_of_pow_eq {q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    {n : ℕ} (hn : 0 < n) (h : r ^ n = q) :
    Real.log r = Real.log q / n := by
  rw [← h, Real.log_pow]
  field_simp

/-- For the paper theta value r ^ (j^2) with r ^ (2l) = q,
log (r ^ (j^2)) = (j^2/(2l)) * log q. -/
theorem log_pow_eq_mul_log_div {q r : ℝ} (hq : 0 < q) (hr : 0 < r)
    {n : ℕ} (hn : 0 < n) (h : r ^ n = q) (j : ℕ) :
    Real.log (r ^ (j ^ 2)) = ((j ^ 2 : ℝ) / n) * Real.log q := by
  rw [Real.log_pow, log_eq_log_div_of_pow_eq hq hr hn h, Nat.cast_pow]
  ring

/-! ## 2. Roots of unity have norm one; the log is mu_n-invariant -/

/-- In any normed field, a nontrivial n-th root of unity has norm one. -/
theorem norm_eq_one_of_pow_eq_one {K : Type*} [NormedField K] {ζ : K} {n : ℕ}
    (hn : 0 < n) (hζ : ζ ^ n = 1) : ‖ζ‖ = 1 := by
  have h : ‖ζ‖ ^ n = 1 := by
    rw [← norm_pow, hζ, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hn.ne').mp h

/-- The p-adic log of a root of unity times r equals the log of r; this is
the exact sense in which the log-volume is mu_{2l}-invariant. -/
theorem log_norm_mul_rootOfUnity_eq {K : Type*} [NormedField K] {ζ : K} {n : ℕ}
    (hn : 0 < n) (hζ : ζ ^ n = 1) (r : K) :
    Real.log ‖ζ * r‖ = Real.log ‖r‖ := by
  rw [norm_mul, norm_eq_one_of_pow_eq_one hn hζ, one_mul]

/-! ## 3. Finite free orbit: the stacky 1/|G| normalization -/

/-- For a finite group G, a left-invariant real function is constant on the
regular orbit; the sum over the orbit is |G| times the value at the base
point.  This is the finite form of the orbifold/stacky averaging formula. -/
theorem sum_left_invariant_eq_card_mul {G : Type*} [Group G] [Fintype G]
    (f : G → ℝ) (hf : ∀ g h, f (g * h) = f h) :
    (∑ g : G, f g) = (Fintype.card G : ℝ) * f 1 := by
  calc
    (∑ g : G, f g) = ∑ _ : G, f 1 := by
      apply Finset.sum_congr rfl
      intro g _
      simpa using hf g 1
    _ = (Fintype.card G : ℝ) * f 1 := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- The stacky average (1/|G|) * sum of a left-invariant function on a free
regular orbit equals the value at one point: no root choice is needed. -/
theorem stacky_average_eq {G : Type*} [Group G] [Fintype G]
    (f : G → ℝ) (hf : ∀ g h, f (g * h) = f h) :
    (1 / (Fintype.card G : ℝ)) * (∑ g : G, f g) = f 1 := by
  rw [sum_left_invariant_eq_card_mul f hf]
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

end LeanFormal.IUT.XiFPaper.TaskFEquivariantOrbifoldKernel