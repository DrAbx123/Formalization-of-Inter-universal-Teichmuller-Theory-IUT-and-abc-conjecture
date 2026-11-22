/-
  Laurent-series terms for the Tate parameterization.

  The two half-series are kept separate.  This is the correct formal shape
  for a non-archimedean Laurent series indexed by `ℤ`: it avoids silently
  replacing a bilateral convergence statement by a natural-number series.
-/

import LeanFormal.IUT.Foundations.Geometry.RigidTateAnnulus
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

namespace LeanFormal.IUT

universe u

noncomputable section

namespace RigidTate

set_option linter.unusedSectionVars false

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

abbrev FundamentalDomain (P : Parameter (K := K)) := Shell P 0

namespace FundamentalDomain

variable (P : Parameter (K := K))

theorem ne_zero (u : FundamentalDomain P) : u.1 ≠ 0 :=
  Shell.ne_zero P 0 u

theorem norm_pos (u : FundamentalDomain P) : 0 < ‖u.1‖ :=
  Shell.norm_pos P 0 u

theorem q_lt_norm (u : FundamentalDomain P) :
    ‖P.q‖ < ‖u.1‖ := by
  simpa using Shell.inner P 0 u

theorem norm_lt_one (u : FundamentalDomain P) :
    ‖u.1‖ < 1 := by
  simpa using Shell.outer P 0 u

end FundamentalDomain

/-- The two radial pieces of the Tate Laurent series. -/
def positiveArgument (P : Parameter (K := K))
    (u : FundamentalDomain P) (n : ℕ) : K :=
  P.q ^ (n : ℤ) * u.1

def negativeArgument (P : Parameter (K := K))
    (u : FundamentalDomain P) (n : ℕ) : K :=
  P.q ^ (-(n + 1 : ℕ) : ℤ) * u.1

namespace Argument

variable (P : Parameter (K := K)) (u : FundamentalDomain P)

@[simp] theorem positiveArgument_zero : positiveArgument P u 0 = u.1 := by
  simp [positiveArgument]

@[simp] theorem positiveArgument_succ (n : ℕ) :
    positiveArgument P u (n + 1) = P.q ^ (n + 1 : ℤ) * u.1 :=
  rfl

theorem positiveArgument_ne_zero (n : ℕ) :
    positiveArgument P u n ≠ 0 := by
  exact mul_ne_zero (Parameter.q_zpow_ne_zero P n) u.ne_zero

theorem positiveArgument_norm (n : ℕ) :
    ‖positiveArgument P u n‖ = ‖P.q‖ ^ (n : ℤ) * ‖u.1‖ := by
  simp [positiveArgument]

theorem positiveArgument_norm_lt_one (n : ℕ) :
    ‖positiveArgument P u n‖ < 1 := by
  rw [positiveArgument_norm]
  have hq : ‖P.q‖ ^ (n : ℤ) ≤ 1 := by
    cases n with
    | zero => simp
    | succ n =>
        exact (Parameter.norm_q_zpow_lt_one P (n + 1 : ℤ) (by omega)).le
  have hu := FundamentalDomain.norm_lt_one P u
  have hq0 : 0 ≤ ‖P.q‖ ^ (n : ℤ) :=
    (Parameter.norm_q_zpow_pos P (n : ℤ)).le
  have hu0 : 0 ≤ ‖u.1‖ := norm_nonneg _
  nlinarith

theorem positiveArgument_sub_one_norm (n : ℕ) :
    ‖1 - positiveArgument P u n‖ = 1 := by
  have harg := positiveArgument_norm_lt_one P u n
  have hupper : ‖1 - positiveArgument P u n‖ ≤ 1 := by
    calc
      ‖1 - positiveArgument P u n‖ ≤
          max ‖(1 : K)‖ ‖positiveArgument P u n‖ := by
        simpa [sub_eq_add_neg] using
          IsUltrametricDist.norm_add_le_max (1 : K)
            (-(positiveArgument P u n))
      _ ≤ 1 := max_le (by simp) harg.le
  have hlower : 1 ≤ ‖1 - positiveArgument P u n‖ := by
    by_contra hnot
    have hlt : ‖1 - positiveArgument P u n‖ < 1 := lt_of_not_ge hnot
    have h1 : (1 : ℝ) ≤
        max ‖1 - positiveArgument P u n‖ ‖positiveArgument P u n‖ := by
      have h := IsUltrametricDist.norm_add_le_max
        (1 - positiveArgument P u n) (positiveArgument P u n)
      rw [sub_add_cancel] at h
      simpa using h
    have h2 : max ‖1 - positiveArgument P u n‖
        ‖positiveArgument P u n‖ < 1 :=
      max_lt hlt harg
    linarith
  exact le_antisymm hupper hlower

theorem positiveArgument_denominator_ne_zero (n : ℕ) :
    1 - positiveArgument P u n ≠ 0 := by
  intro h
  have hnorm := congrArg norm h
  rw [norm_zero, positiveArgument_sub_one_norm P u n] at hnorm
  norm_num at hnorm

theorem positiveArgument_sub_one_inverse_norm (n : ℕ) :
    ‖(1 - positiveArgument P u n)⁻¹‖ = 1 := by
  rw [norm_inv, positiveArgument_sub_one_norm P u n, inv_one]

theorem negativeArgument_ne_zero (n : ℕ) :
    negativeArgument P u n ≠ 0 := by
  exact mul_ne_zero (Parameter.q_zpow_ne_zero P (-(n + 1 : ℕ) : ℤ)) u.ne_zero

theorem negativeArgument_norm (n : ℕ) :
    ‖negativeArgument P u n‖ =
      (‖P.q‖ ^ (n + 1 : ℤ))⁻¹ * ‖u.1‖ := by
  rw [negativeArgument, norm_mul, Parameter.norm_q_zpow, zpow_neg,
    Nat.cast_add, Nat.cast_one]

theorem negativeArgument_norm_gt_one (n : ℕ) :
    1 < ‖negativeArgument P u n‖ := by
  rw [negativeArgument_norm]
  have hqpos : 0 < ‖P.q‖ ^ (n + 1 : ℤ) :=
    Parameter.norm_q_zpow_pos P (n + 1 : ℤ)
  have hinner : ‖P.q‖ ^ (n + 1 : ℤ) < ‖u.1‖ := by
    have hle : ‖P.q‖ ^ (n + 1 : ℤ) ≤ ‖P.q‖ ^ (1 : ℤ) :=
      zpow_le_zpow_right_of_le_one₀ P.q_norm_pos P.q_norm_lt_one.le (by omega)
    rw [zpow_one] at hle
    exact hle.trans_lt (by simpa using Shell.inner P 0 u)
  have hdiv : 1 < ‖u.1‖ / ‖P.q‖ ^ (n + 1 : ℤ) := by
    apply (lt_div_iff₀ hqpos).2
    simpa using hinner
  simpa [div_eq_mul_inv, mul_comm] using hdiv

theorem negativeArgument_sub_one_norm (n : ℕ) :
    ‖1 - negativeArgument P u n‖ = ‖negativeArgument P u n‖ := by
  have harg := negativeArgument_norm_gt_one P u n
  have hupper : ‖1 - negativeArgument P u n‖ ≤
      ‖negativeArgument P u n‖ := by
    calc
      ‖1 - negativeArgument P u n‖ ≤
          max ‖(1 : K)‖ ‖negativeArgument P u n‖ := by
        simpa [sub_eq_add_neg] using
          IsUltrametricDist.norm_add_le_max (1 : K)
            (-(negativeArgument P u n))
      _ ≤ ‖negativeArgument P u n‖ :=
        max_le (by simpa using le_of_lt harg) le_rfl
  have hlower : ‖negativeArgument P u n‖ ≤
      ‖1 - negativeArgument P u n‖ := by
    by_contra hnot
    have hlt : ‖1 - negativeArgument P u n‖ <
        ‖negativeArgument P u n‖ := lt_of_not_ge hnot
    have h1 : ‖negativeArgument P u n‖ ≤
        max 1 ‖1 - negativeArgument P u n‖ := by
      have h := IsUltrametricDist.norm_add_le_max (1 : K)
        (negativeArgument P u n - 1)
      have heq : (1 : K) + (negativeArgument P u n - 1) =
          negativeArgument P u n := by ring
      rw [heq] at h
      have hneg : ‖negativeArgument P u n - 1‖ =
          ‖1 - negativeArgument P u n‖ := by
        have : negativeArgument P u n - 1 =
            -(1 - negativeArgument P u n) := by ring
        rw [this, norm_neg]
      rw [hneg] at h
      simpa using h
    have h2 : max 1 ‖1 - negativeArgument P u n‖ <
        ‖negativeArgument P u n‖ :=
      max_lt harg hlt
    linarith
  exact le_antisymm hupper hlower

theorem negativeArgument_denominator_ne_zero (n : ℕ) :
    1 - negativeArgument P u n ≠ 0 := by
  intro h
  have hnorm := congrArg norm h
  rw [norm_zero, negativeArgument_sub_one_norm P u n] at hnorm
  have hpos := negativeArgument_norm_gt_one P u n
  linarith

end Argument

def xPositiveTerm (P : Parameter (K := K))
    (u : FundamentalDomain P) (n : ℕ) : K :=
  positiveArgument P u n /
    (1 - positiveArgument P u n) ^ 2

def xNegativeTerm (P : Parameter (K := K))
    (u : FundamentalDomain P) (n : ℕ) : K :=
  negativeArgument P u n /
    (1 - negativeArgument P u n) ^ 2

def yPositiveTerm (P : Parameter (K := K))
    (u : FundamentalDomain P) (n : ℕ) : K :=
  positiveArgument P u n ^ 2 /
    (1 - positiveArgument P u n) ^ 3

def yNegativeTerm (P : Parameter (K := K))
    (u : FundamentalDomain P) (n : ℕ) : K :=
  negativeArgument P u n ^ 2 /
    (1 - negativeArgument P u n) ^ 3

namespace Term

variable (P : Parameter (K := K)) (u : FundamentalDomain P)

theorem xPositiveTerm_norm_le (n : ℕ) :
    ‖xPositiveTerm P u n‖ ≤ ‖P.q‖ ^ (n : ℤ) * ‖u.1‖ := by
  simp only [xPositiveTerm, norm_div, norm_pow,
    Argument.positiveArgument_sub_one_norm P u n,
    Argument.positiveArgument_norm]
  simp

theorem yPositiveTerm_norm_le (n : ℕ) :
    ‖yPositiveTerm P u n‖ ≤
      (‖P.q‖ ^ (n : ℤ) * ‖u.1‖) ^ 2 := by
  simp only [yPositiveTerm, norm_div, norm_pow,
    Argument.positiveArgument_sub_one_norm P u n,
    Argument.positiveArgument_norm]
  simp

theorem xNegativeTerm_norm (n : ℕ) :
    ‖xNegativeTerm P u n‖ =
      (‖P.q‖ ^ (n + 1 : ℤ)) * ‖u.1‖⁻¹ := by
  have hgt := Argument.negativeArgument_norm_gt_one P u n
  have hne : ‖negativeArgument P u n‖ ≠ 0 := ne_of_gt (zero_lt_one.trans hgt)
  have hsub := Argument.negativeArgument_sub_one_norm P u n
  rw [xNegativeTerm, norm_div, norm_pow, hsub]
  have hkey : ‖negativeArgument P u n‖ / ‖negativeArgument P u n‖ ^ 2 =
      ‖negativeArgument P u n‖⁻¹ := by
    rw [div_eq_mul_inv, pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hne,
      one_mul]
  rw [hkey, Argument.negativeArgument_norm, mul_inv_rev, inv_inv, mul_comm]

theorem yNegativeTerm_norm (n : ℕ) :
    ‖yNegativeTerm P u n‖ =
      (‖P.q‖ ^ (n + 1 : ℤ)) * ‖u.1‖⁻¹ := by
  have hgt := Argument.negativeArgument_norm_gt_one P u n
  have hne : ‖negativeArgument P u n‖ ≠ 0 := ne_of_gt (zero_lt_one.trans hgt)
  have hsub := Argument.negativeArgument_sub_one_norm P u n
  simp only [yNegativeTerm, norm_div, norm_pow, hsub]
  have hkey : ‖negativeArgument P u n‖ ^ 2 / ‖negativeArgument P u n‖ ^ 3 =
      ‖negativeArgument P u n‖⁻¹ := by
    have h3 : ‖negativeArgument P u n‖ ^ 3 =
        ‖negativeArgument P u n‖ ^ 2 * ‖negativeArgument P u n‖ := by ring
    rw [div_eq_mul_inv, h3, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero 2 hne), one_mul]
  rw [hkey, Argument.negativeArgument_norm, mul_inv_rev, inv_inv, mul_comm]

variable [CompleteSpace K]

/-- The one-sided x-positive terms are summable, dominated by the geometric
majorant `‖u.1‖ * ‖q‖ ^ n`. -/
theorem xPositiveTerm_summable :
    Summable (fun n : ℕ => xPositiveTerm P u n) := by
  refine (Summable.mul_left ‖u.1‖
    (summable_geometric_of_lt_one (norm_nonneg P.q) P.q_norm_lt_one)).of_norm_bounded
      (fun n => ?_)
  calc ‖xPositiveTerm P u n‖ ≤ ‖P.q‖ ^ (n : ℤ) * ‖u.1‖ := xPositiveTerm_norm_le P u n
    _ = ‖u.1‖ * ‖P.q‖ ^ n := by rw [zpow_natCast, mul_comm]

/-- The one-sided y-positive terms are summable, dominated by the geometric
majorant `‖u.1‖ ^ 2 * (‖q‖ ^ 2) ^ n`. -/
theorem yPositiveTerm_summable :
    Summable (fun n : ℕ => yPositiveTerm P u n) := by
  have hq2 : ‖P.q‖ ^ 2 < 1 := by nlinarith [norm_nonneg P.q, P.q_norm_lt_one]
  refine (Summable.mul_left (‖u.1‖ ^ 2)
    (summable_geometric_of_lt_one (sq_nonneg ‖P.q‖) hq2)).of_norm_bounded
      (fun n => ?_)
  calc ‖yPositiveTerm P u n‖ ≤ (‖P.q‖ ^ (n : ℤ) * ‖u.1‖) ^ 2 :=
        yPositiveTerm_norm_le P u n
    _ = ‖u.1‖ ^ 2 * (‖P.q‖ ^ 2) ^ n := by
        rw [zpow_natCast, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm n 2]
        ring

/-- The one-sided x-negative terms are summable, dominated by the geometric
majorant `(‖q‖ * ‖u.1‖⁻¹) * ‖q‖ ^ n`. -/
theorem xNegativeTerm_summable :
    Summable (fun n : ℕ => xNegativeTerm P u n) := by
  have hpow : ∀ n : ℕ, ‖P.q‖ ^ (n + 1 : ℤ) = ‖P.q‖ ^ n * ‖P.q‖ := fun n => by
    rw [zpow_add₀ P.q_norm_ne_zero, zpow_natCast, zpow_one]
  refine (Summable.mul_left (‖P.q‖ * ‖u.1‖⁻¹)
    (summable_geometric_of_lt_one (norm_nonneg P.q) P.q_norm_lt_one)).of_norm_bounded
      (fun n => ?_)
  have hkey : ‖xNegativeTerm P u n‖ = (‖P.q‖ * ‖u.1‖⁻¹) * ‖P.q‖ ^ n := by
    rw [xNegativeTerm_norm P u n, hpow n]
    ring
  exact hkey.le

/-- The one-sided y-negative terms are summable, with the same geometric
majorant as the x-negative terms. -/
theorem yNegativeTerm_summable :
    Summable (fun n : ℕ => yNegativeTerm P u n) := by
  have hpow : ∀ n : ℕ, ‖P.q‖ ^ (n + 1 : ℤ) = ‖P.q‖ ^ n * ‖P.q‖ := fun n => by
    rw [zpow_add₀ P.q_norm_ne_zero, zpow_natCast, zpow_one]
  refine (Summable.mul_left (‖P.q‖ * ‖u.1‖⁻¹)
    (summable_geometric_of_lt_one (norm_nonneg P.q) P.q_norm_lt_one)).of_norm_bounded
      (fun n => ?_)
  have hkey : ‖yNegativeTerm P u n‖ = (‖P.q‖ * ‖u.1‖⁻¹) * ‖P.q‖ ^ n := by
    rw [yNegativeTerm_norm P u n, hpow n]
    ring
  exact hkey.le

end Term

/-- One-sided sums are the actual convergent pieces of the Tate x-coordinate. -/
def xPositiveSeries (P : Parameter (K := K))
    (u : FundamentalDomain P) : K :=
  ∑' n : ℕ, xPositiveTerm P u n

def xNegativeSeries (P : Parameter (K := K))
    (u : FundamentalDomain P) : K :=
  ∑' n : ℕ, xNegativeTerm P u n

def yPositiveSeries (P : Parameter (K := K))
    (u : FundamentalDomain P) : K :=
  ∑' n : ℕ, yPositiveTerm P u n

def yNegativeSeries (P : Parameter (K := K))
    (u : FundamentalDomain P) : K :=
  ∑' n : ℕ, yNegativeTerm P u n

variable [CompleteSpace K]

/-! ## Convergence of the four one-sided sums -/

/-- `xPositiveSeries` is the sum of the summable x-positive terms. -/
theorem hasSum_xPositiveSeries (P : Parameter (K := K)) (u : FundamentalDomain P) :
    HasSum (fun n : ℕ => xPositiveTerm P u n) (xPositiveSeries P u) := by
  simpa only [xPositiveSeries] using (Term.xPositiveTerm_summable P u).hasSum

/-- `xNegativeSeries` is the sum of the summable x-negative terms. -/
theorem hasSum_xNegativeSeries (P : Parameter (K := K)) (u : FundamentalDomain P) :
    HasSum (fun n : ℕ => xNegativeTerm P u n) (xNegativeSeries P u) := by
  simpa only [xNegativeSeries] using (Term.xNegativeTerm_summable P u).hasSum

/-- `yPositiveSeries` is the sum of the summable y-positive terms. -/
theorem hasSum_yPositiveSeries (P : Parameter (K := K)) (u : FundamentalDomain P) :
    HasSum (fun n : ℕ => yPositiveTerm P u n) (yPositiveSeries P u) := by
  simpa only [yPositiveSeries] using (Term.yPositiveTerm_summable P u).hasSum

/-- `yNegativeSeries` is the sum of the summable y-negative terms. -/
theorem hasSum_yNegativeSeries (P : Parameter (K := K)) (u : FundamentalDomain P) :
    HasSum (fun n : ℕ => yNegativeTerm P u n) (yNegativeSeries P u) := by
  simpa only [yNegativeSeries] using (Term.yNegativeTerm_summable P u).hasSum

end RigidTate

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def rigidTateLaurentTerms : Obligation :=
  { id := "Foundations.Geometry.rigid-tate-laurent-terms"
    source := "Tate uniformization: Laurent coordinate terms on |q|<|u|<1"
    status := VerificationStatus.interface
    note :=
      "The two-sided Tate x/y summands are defined on the genuine " ++
        "non-archimedean fundamental annulus, with proved nonvanishing " ++
        "denominators and radial norm estimates. The remaining summability " ++
        "and the Weierstrass equation identity are the next analytic proof " ++
        "obligations; no point map is claimed yet."
    dependsOn := [ "Foundations.Geometry.rigid-tate-annulus" ] }

end LeanFormal.IUT.Audit
