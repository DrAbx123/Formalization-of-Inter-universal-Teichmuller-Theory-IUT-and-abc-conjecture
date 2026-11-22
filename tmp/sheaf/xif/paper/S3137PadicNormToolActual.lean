import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

/-!
# TOOL: generic p-adic norm computations (generic)

**Reusable mathematical tool, not a paper object.**  Owner: lattice.  Companion
to the M2a base-norm computation: for any prime `p`, the canonical p-adic norm
of the integer `p` is `p⁻¹`, its powers have norm `p^{-n}`, and a nonzero
element with that norm exists.  These are the generic padic norm facts that the
normalized-completion comparisons need, stated for arbitrary `p` so that any
consumer (qpilot M2a, mainline normalization, lattice q-pilot readings) can
instantiate them without repeating Mathlib plumbing.

Sources: IUT I, Example 3.2, (iv); IUT III, Definition 3.8, (i), p. 112;
Mathlib `Padic.norm_p`, `Padic.norm_p_zpow`, `Padic.norm_p_pow`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.PadicNormToolActual

local instance factPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Generic tool: the p-adic canonical norm of the integer prime `p` is `p⁻¹`. -/
theorem padic_norm_prime (p : ℕ) [Fact p.Prime] :
    ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹ :=
  Padic.norm_p

/-- Generic tool: integer powers of the prime have norm `p^{-n}`. -/
theorem padic_norm_prime_zpow (p : ℕ) [Fact p.Prime] (n : ℤ) :
    ‖(p : ℚ_[p]) ^ n‖ = (p : ℝ) ^ (-n) :=
  Padic.norm_p_zpow n

/-- Generic tool: natural powers of the prime have norm `p^{-n}`. -/
theorem padic_norm_prime_pow (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ‖(p : ℚ_[p]) ^ n‖ = (p : ℝ) ^ (-n : ℤ) :=
  Padic.norm_p_pow n

/-- Generic tool: the prime itself is a nonzero element of `ℚ_[p]`. -/
theorem padic_prime_ne_zero (p : ℕ) [Fact p.Prime] : (p : ℚ_[p]) ≠ 0 := by
  intro h
  have hnorm : ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹ := padic_norm_prime p
  rw [h, norm_zero] at hnorm
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  exact (inv_ne_zero hp.ne') hnorm.symm

/-- Generic tool: existence of a nonzero p-adic element with norm `p⁻¹` (the
base-field norm computation shape, cf. qpilot M2a `S3133RationalFiveCompletionNorm`
when the rational completion is identified with `ℚ_[p]`). -/
theorem exists_padic_norm_prime_inv (p : ℕ) [Fact p.Prime] :
    ∃ x : ℚ_[p], x ≠ 0 ∧ ‖x‖ = (p : ℝ)⁻¹ :=
  ⟨(p : ℚ_[p]), padic_prime_ne_zero p, padic_norm_prime p⟩

/-- Generic tool, five-adic instance: the canonical 5-adic norm of 5 is `1/5`. -/
theorem padic_norm_five : ‖(5 : ℚ_[5])‖ = ((5 : ℝ)⁻¹) :=
  padic_norm_prime 5

end LeanFormal.IUT.XiFPaper.PadicNormToolActual