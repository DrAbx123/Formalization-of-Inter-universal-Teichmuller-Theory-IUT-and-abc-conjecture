import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Legendre parameter symmetries and exact fibers

This file concerns the rational function of a Legendre parameter. Its intended
consumer is the parameter-to-moduli step of the IUT IV GenEll/Vjt specialization.
Identification with the invariant of an actual Weierstrass curve is a separate
statement. Equality of the function values here makes no assertion about
isomorphism over the ground field.

The cleared numerator difference has six linear factors. Their roots are the
usual six transforms, with repetitions allowed. Consequently every fiber on
the admissible domain has at most six elements, including special parameters
where some transforms coincide.
-/

namespace LeanFormal.IUT

variable {K : Type*} [Field K] [CharZero K]

/-- The nonsingular parameter domain for the Legendre family. -/
def IsLegendreParameter (lambda : K) : Prop :=
  lambda ≠ 0 ∧ lambda ≠ 1

/-- The parameter-side rational expression for the Legendre invariant. -/
def legendreJParameter (lambda : K) : K :=
  256 * (lambda ^ 2 - lambda + 1) ^ 3 /
    (lambda ^ 2 * (1 - lambda) ^ 2)

theorem isLegendreParameter_one_sub {lambda : K}
    (admissible : IsLegendreParameter lambda) :
    IsLegendreParameter (1 - lambda) := by
  constructor
  · exact sub_ne_zero.mpr (Ne.symm admissible.2)
  · intro complement_eq_one
    apply admissible.1
    linear_combination -complement_eq_one

theorem isLegendreParameter_one_div {lambda : K}
    (admissible : IsLegendreParameter lambda) :
    IsLegendreParameter (1 / lambda) := by
  constructor
  · exact one_div_ne_zero admissible.1
  · intro reciprocal_eq_one
    apply admissible.2
    have cleared_reciprocal :=
      (eq_div_iff admissible.1).mp reciprocal_eq_one.symm
    simpa using cleared_reciprocal

theorem isLegendreParameter_one_div_one_sub {lambda : K}
    (admissible : IsLegendreParameter lambda) :
    IsLegendreParameter (1 / (1 - lambda)) :=
  isLegendreParameter_one_div (isLegendreParameter_one_sub admissible)

theorem isLegendreParameter_div_sub_one {lambda : K}
    (admissible : IsLegendreParameter lambda) :
    IsLegendreParameter (lambda / (lambda - 1)) := by
  have denominator_ne_zero : lambda - 1 ≠ 0 :=
    sub_ne_zero.mpr admissible.2
  constructor
  · exact div_ne_zero admissible.1 denominator_ne_zero
  · intro quotient_eq_one
    have cleared_quotient := (div_eq_iff denominator_ne_zero).mp quotient_eq_one
    have one_eq_zero : (1 : K) = 0 := by
      linear_combination cleared_quotient
    exact one_ne_zero one_eq_zero

theorem isLegendreParameter_sub_one_div {lambda : K}
    (admissible : IsLegendreParameter lambda) :
    IsLegendreParameter ((lambda - 1) / lambda) := by
  constructor
  · exact div_ne_zero (sub_ne_zero.mpr admissible.2) admissible.1
  · intro quotient_eq_one
    have cleared_quotient := (div_eq_iff admissible.1).mp quotient_eq_one
    have one_eq_zero : (1 : K) = 0 := by
      linear_combination -cleared_quotient
    exact one_ne_zero one_eq_zero

theorem legendreParameterDenominator_ne_zero {lambda : K}
    (admissible : IsLegendreParameter lambda) :
    lambda ^ 2 * (1 - lambda) ^ 2 ≠ 0 :=
  mul_ne_zero (pow_ne_zero 2 admissible.1)
    (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm admissible.2)))

/-- The polynomial identity underlying the exact, possibly repeated, six roots. -/
theorem legendreParameter_cleared_factorization (lambda mu : K) :
    (mu ^ 2 - mu + 1) ^ 3 * (lambda ^ 2 * (1 - lambda) ^ 2) -
        (lambda ^ 2 - lambda + 1) ^ 3 * (mu ^ 2 * (1 - mu) ^ 2) =
      (mu - lambda) * (mu + lambda - 1) * (mu * lambda - 1) *
        (mu * (1 - lambda) - 1) * (mu * (1 - lambda) + lambda) *
        (mu * lambda + 1 - lambda) := by
  ring

/-- Clearing denominators is legitimate at both admissible parameters. -/
theorem legendreJParameter_eq_iff_factorProduct_eq_zero {lambda mu : K}
    (lambda_admissible : IsLegendreParameter lambda)
    (mu_admissible : IsLegendreParameter mu) :
    legendreJParameter mu = legendreJParameter lambda ↔
      (mu - lambda) * (mu + lambda - 1) * (mu * lambda - 1) *
        (mu * (1 - lambda) - 1) * (mu * (1 - lambda) + lambda) *
        (mu * lambda + 1 - lambda) = 0 := by
  rw [legendreJParameter, legendreJParameter,
    div_eq_div_iff (legendreParameterDenominator_ne_zero mu_admissible)
      (legendreParameterDenominator_ne_zero lambda_admissible)]
  constructor
  · intro cross_multiplied_equality
    have scaled_difference :
        (256 : K) *
          ((mu ^ 2 - mu + 1) ^ 3 * (lambda ^ 2 * (1 - lambda) ^ 2) -
            (lambda ^ 2 - lambda + 1) ^ 3 * (mu ^ 2 * (1 - mu) ^ 2)) = 0 := by
      linear_combination cross_multiplied_equality
    have numerator_difference :
        (mu ^ 2 - mu + 1) ^ 3 * (lambda ^ 2 * (1 - lambda) ^ 2) -
          (lambda ^ 2 - lambda + 1) ^ 3 * (mu ^ 2 * (1 - mu) ^ 2) = 0 :=
      (mul_eq_zero.mp scaled_difference).resolve_left (by norm_num)
    rw [legendreParameter_cleared_factorization] at numerator_difference
    exact numerator_difference
  · intro factors_vanish
    have numerator_difference :
        (mu ^ 2 - mu + 1) ^ 3 * (lambda ^ 2 * (1 - lambda) ^ 2) -
          (lambda ^ 2 - lambda + 1) ^ 3 * (mu ^ 2 * (1 - mu) ^ 2) = 0 := by
      rw [legendreParameter_cleared_factorization]
      exact factors_vanish
    linear_combination (256 : K) * numerator_difference

/-- Exact fibers, stated without assuming that the six transforms are distinct. -/
theorem legendreJParameter_eq_iff_six_transforms {lambda mu : K}
    (lambda_admissible : IsLegendreParameter lambda)
    (mu_admissible : IsLegendreParameter mu) :
    legendreJParameter mu = legendreJParameter lambda ↔
      mu = lambda ∨ mu = 1 - lambda ∨ mu = 1 / lambda ∨
        mu = 1 / (1 - lambda) ∨ mu = lambda / (lambda - 1) ∨
        mu = (lambda - 1) / lambda := by
  rw [legendreJParameter_eq_iff_factorProduct_eq_zero
    lambda_admissible mu_admissible]
  have complement_ne_zero : 1 - lambda ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm lambda_admissible.2)
  have difference_ne_zero : lambda - 1 ≠ 0 :=
    sub_ne_zero.mpr lambda_admissible.2
  simp only [mul_eq_zero, or_assoc]
  constructor
  · intro vanishing_factor
    rcases vanishing_factor with same | complement | reciprocal |
      reciprocal_complement | quotient | shifted_quotient
    · exact Or.inl (sub_eq_zero.mp same)
    · right; left
      linear_combination complement
    · right; right; left
      exact (eq_div_iff lambda_admissible.1).mpr (sub_eq_zero.mp reciprocal)
    · right; right; right; left
      exact (eq_div_iff complement_ne_zero).mpr (sub_eq_zero.mp reciprocal_complement)
    · right; right; right; right; left
      apply (eq_div_iff difference_ne_zero).mpr
      linear_combination -quotient
    · right; right; right; right; right
      apply (eq_div_iff lambda_admissible.1).mpr
      linear_combination shifted_quotient
  · intro transform_equality
    rcases transform_equality with same | complement | reciprocal |
      reciprocal_complement | quotient | shifted_quotient
    · exact Or.inl (sub_eq_zero.mpr same)
    · right; left
      linear_combination complement
    · right; right; left
      exact sub_eq_zero.mpr ((eq_div_iff lambda_admissible.1).mp reciprocal)
    · right; right; right; left
      exact sub_eq_zero.mpr ((eq_div_iff complement_ne_zero).mp reciprocal_complement)
    · right; right; right; right; left
      have cleared_quotient := (eq_div_iff difference_ne_zero).mp quotient
      linear_combination -cleared_quotient
    · right; right; right; right; right
      have cleared_quotient := (eq_div_iff lambda_admissible.1).mp shifted_quotient
      linear_combination cleared_quotient

theorem legendreJParameter_one_sub {lambda : K}
    (admissible : IsLegendreParameter lambda) :
    legendreJParameter (1 - lambda) = legendreJParameter lambda :=
  (legendreJParameter_eq_iff_six_transforms admissible
    (isLegendreParameter_one_sub admissible)).mpr (Or.inr (Or.inl rfl))

theorem legendreJParameter_one_div {lambda : K}
    (admissible : IsLegendreParameter lambda) :
    legendreJParameter (1 / lambda) = legendreJParameter lambda :=
  (legendreJParameter_eq_iff_six_transforms admissible
    (isLegendreParameter_one_div admissible)).mpr (Or.inr (Or.inr (Or.inl rfl)))

theorem legendreJParameter_one_div_one_sub {lambda : K}
    (admissible : IsLegendreParameter lambda) :
    legendreJParameter (1 / (1 - lambda)) = legendreJParameter lambda :=
  (legendreJParameter_eq_iff_six_transforms admissible
    (isLegendreParameter_one_div_one_sub admissible)).mpr
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem legendreJParameter_div_sub_one {lambda : K}
    (admissible : IsLegendreParameter lambda) :
    legendreJParameter (lambda / (lambda - 1)) = legendreJParameter lambda :=
  (legendreJParameter_eq_iff_six_transforms admissible
    (isLegendreParameter_div_sub_one admissible)).mpr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

theorem legendreJParameter_sub_one_div {lambda : K}
    (admissible : IsLegendreParameter lambda) :
    legendreJParameter ((lambda - 1) / lambda) = legendreJParameter lambda :=
  (legendreJParameter_eq_iff_six_transforms admissible
    (isLegendreParameter_sub_one_div admissible)).mpr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

/-- The six transforms as a finite set, automatically removing collisions. -/
noncomputable def legendreParameterTransforms (lambda : K) : Finset K := by
  classical
  exact [lambda, 1 - lambda, 1 / lambda, 1 / (1 - lambda),
    lambda / (lambda - 1), (lambda - 1) / lambda].toFinset

theorem mem_legendreParameterTransforms (lambda mu : K) :
    mu ∈ legendreParameterTransforms lambda ↔
      mu = lambda ∨ mu = 1 - lambda ∨ mu = 1 / lambda ∨
        mu = 1 / (1 - lambda) ∨ mu = lambda / (lambda - 1) ∨
        mu = (lambda - 1) / lambda := by
  classical
  simp [legendreParameterTransforms]

theorem legendreParameterTransforms_card_le_six (lambda : K) :
    (legendreParameterTransforms lambda).card ≤ 6 := by
  classical
  simpa [legendreParameterTransforms] using
    (List.toFinset_card_le [lambda, 1 - lambda, 1 / lambda, 1 / (1 - lambda),
      lambda / (lambda - 1), (lambda - 1) / lambda])

theorem isLegendreParameter_of_mem_transforms {lambda mu : K}
    (lambda_admissible : IsLegendreParameter lambda)
    (membership : mu ∈ legendreParameterTransforms lambda) :
    IsLegendreParameter mu := by
  rcases (mem_legendreParameterTransforms lambda mu).mp membership with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact lambda_admissible
  · exact isLegendreParameter_one_sub lambda_admissible
  · exact isLegendreParameter_one_div lambda_admissible
  · exact isLegendreParameter_one_div_one_sub lambda_admissible
  · exact isLegendreParameter_div_sub_one lambda_admissible
  · exact isLegendreParameter_sub_one_div lambda_admissible

theorem legendreJParameter_eq_iff_mem_transforms {lambda mu : K}
    (lambda_admissible : IsLegendreParameter lambda)
    (mu_admissible : IsLegendreParameter mu) :
    legendreJParameter mu = legendreJParameter lambda ↔
      mu ∈ legendreParameterTransforms lambda :=
  (legendreJParameter_eq_iff_six_transforms lambda_admissible mu_admissible).trans
    (mem_legendreParameterTransforms lambda mu).symm

/-- A fiber over an arbitrary field value, restricted to admissible parameters. -/
def legendreJParameterFiber (jValue : K) : Set K :=
  {lambda | IsLegendreParameter lambda ∧ legendreJParameter lambda = jValue}

theorem legendreJParameterFiber_eq_transforms {lambda : K}
    (lambda_admissible : IsLegendreParameter lambda) :
    legendreJParameterFiber (legendreJParameter lambda) =
      (↑(legendreParameterTransforms lambda) : Set K) := by
  ext mu
  change (IsLegendreParameter mu ∧ legendreJParameter mu = legendreJParameter lambda) ↔
    mu ∈ legendreParameterTransforms lambda
  constructor
  · rintro ⟨mu_admissible, same_invariant⟩
    exact (legendreJParameter_eq_iff_mem_transforms
      lambda_admissible mu_admissible).mp same_invariant
  · intro membership
    have mu_admissible := isLegendreParameter_of_mem_transforms lambda_admissible membership
    exact ⟨mu_admissible, (legendreJParameter_eq_iff_mem_transforms
      lambda_admissible mu_admissible).mpr membership⟩

/-- A nonempty fiber is exactly the transform set of any parameter it contains. -/
theorem legendreJParameterFiber_eq_empty_or_eq_transforms (jValue : K) :
    legendreJParameterFiber jValue = ∅ ∨
      ∃ lambda : K, IsLegendreParameter lambda ∧
        legendreJParameterFiber jValue = (↑(legendreParameterTransforms lambda) : Set K) := by
  classical
  by_cases inhabited_fiber : (legendreJParameterFiber jValue).Nonempty
  · obtain ⟨lambda, lambda_in_fiber⟩ := inhabited_fiber
    right
    refine ⟨lambda, lambda_in_fiber.1, ?_⟩
    rw [← lambda_in_fiber.2]
    exact legendreJParameterFiber_eq_transforms lambda_in_fiber.1
  · left
    ext lambda
    constructor
    · intro lambda_in_fiber
      exact (inhabited_fiber ⟨lambda, lambda_in_fiber⟩).elim
    · intro lambda_in_empty
      exact lambda_in_empty.elim

theorem legendreJParameterFiber_finite (jValue : K) :
    (legendreJParameterFiber jValue).Finite := by
  rcases legendreJParameterFiber_eq_empty_or_eq_transforms jValue with
    empty_fiber | ⟨lambda, _, identified_fiber⟩
  · rw [empty_fiber]
    exact Set.finite_empty
  · rw [identified_fiber]
    exact (legendreParameterTransforms lambda).finite_toSet

/-- The bound holds for every target, without genericity or distinct-root assumptions. -/
theorem legendreJParameterFiber_ncard_le_six (jValue : K) :
    (legendreJParameterFiber jValue).ncard ≤ 6 := by
  rcases legendreJParameterFiber_eq_empty_or_eq_transforms jValue with
    empty_fiber | ⟨lambda, _, identified_fiber⟩
  · rw [empty_fiber]
    simp
  · rw [identified_fiber, Set.ncard_coe_finset]
    exact legendreParameterTransforms_card_le_six lambda

/-- Changing the admissible parameter without changing its invariant preserves its orbit. -/
theorem legendreParameterTransforms_eq_of_same_invariant {lambda mu : K}
    (lambda_admissible : IsLegendreParameter lambda)
    (mu_admissible : IsLegendreParameter mu)
    (same_invariant : legendreJParameter mu = legendreJParameter lambda) :
    legendreParameterTransforms mu = legendreParameterTransforms lambda := by
  classical
  apply Finset.coe_injective
  rw [← legendreJParameterFiber_eq_transforms mu_admissible,
    ← legendreJParameterFiber_eq_transforms lambda_admissible, same_invariant]

end LeanFormal.IUT
