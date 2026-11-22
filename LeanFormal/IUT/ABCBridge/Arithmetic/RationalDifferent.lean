import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Rational logarithmic discriminant arithmetic

The intended consumer is the rational-point specialization of IUT IV, Corollary 2.3.
This file works with Mathlib's actual number-field discriminant and root discriminant.
The existing theorem `Rat.numberField_discr` already proves `NumberField.discr ℚ = 1`,
and `NumberField.rootDiscr_rat` already proves `NumberField.rootDiscr ℚ = 1`.

The logarithm of the root discriminant is the logarithm of the absolute discriminant
normalized by the field degree. Both expressions vanish over `ℚ`. These arithmetic
identities alone do not identify the geometric `log-diff_X(x)` in the paper: that
requires the actual definition of the point's field and its geometric normalization.

The different ideal used here is `differentIdeal ℤ (𝓞 K)`. Mathlib already proves
`NumberField.absNorm_differentIdeal`, identifying its absolute norm with
`(NumberField.discr K).natAbs`. No surrogate different is introduced.
-/

namespace IUT.ABCBridge.Arithmetic.RationalDifferent

open NumberField IsDedekindDomain

/-- A number field of degree one is algebraically equivalent to `ℚ` through its
actual rational algebra map. -/
noncomputable def ratAlgEquivOfFinrankOne
    (K : Type*) [Field K] [NumberField K]
    (degree_one : Module.finrank ℚ K = 1) : ℚ ≃ₐ[ℚ] K :=
  AlgEquiv.ofBijective (Algebra.ofId ℚ K)
    ⟨(algebraMap ℚ K).injective, by
      change Function.Surjective (Algebra.linearMap ℚ K)
      rw [← LinearMap.range_eq_top]
      apply Submodule.eq_top_of_finrank_eq
      calc
        Module.finrank ℚ (LinearMap.range (Algebra.linearMap ℚ K)) =
            Module.finrank ℚ ℚ :=
          (LinearEquiv.finrank_eq (LinearEquiv.ofInjective
            (Algebra.linearMap ℚ K) (algebraMap ℚ K).injective)).symm
        _ = Module.finrank ℚ K := by simpa using degree_one.symm⟩

/-- The actual discriminant of a degree-one number field is one. -/
theorem discr_eq_one_of_finrank_one
    (K : Type*) [Field K] [NumberField K]
    (degree_one : Module.finrank ℚ K = 1) : NumberField.discr K = 1 := by
  calc
    NumberField.discr K = NumberField.discr ℚ :=
      NumberField.discr_eq_discr_of_algEquiv K
        (ratAlgEquivOfFinrankOne K degree_one).symm
    _ = 1 := Rat.numberField_discr

/-- In degree one the actual different ideal of the ring of integers is the
unit ideal. This is stronger than vanishing of its logarithmic norm. -/
theorem differentIdeal_eq_top_of_finrank_one
    (K : Type*) [Field K] [NumberField K]
    (degree_one : Module.finrank ℚ K = 1) :
    differentIdeal ℤ (𝓞 K) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  simpa only [discr_eq_one_of_finrank_one K degree_one, Int.cast_one] using
    NumberField.discr_mem_differentIdeal K (𝓞 K)

/-- The absolute norm of the actual different ideal is one in degree one. -/
theorem absNorm_differentIdeal_eq_one_of_finrank_one
    (K : Type*) [Field K] [NumberField K]
    (degree_one : Module.finrank ℚ K = 1) :
    (differentIdeal ℤ (𝓞 K)).absNorm = 1 := by
  rw [NumberField.absNorm_differentIdeal K (𝓞 K),
    discr_eq_one_of_finrank_one K degree_one]
  rfl

/-- The two standard logarithmic normalizations of the actual number-field
absolute discriminant agree. -/
theorem log_rootDiscr_eq_log_abs_discr_div_finrank
    (K : Type*) [Field K] [NumberField K] :
    Real.log (NumberField.rootDiscr K) =
      Real.log |(NumberField.discr K : ℝ)| / (Module.finrank ℚ K : ℝ) := by
  have absoluteDiscriminant_pos : 0 < |(NumberField.discr K : ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast NumberField.discr_ne_zero K
  rw [NumberField.rootDiscr_def, Int.cast_abs, Real.log_rpow absoluteDiscriminant_pos]
  simp only [div_eq_mul_inv, mul_comm]

/-- The degree-normalized logarithm of the norm of the actual different ideal
is the logarithm of the root discriminant. -/
theorem log_absNorm_differentIdeal_div_finrank_eq_log_rootDiscr
    (K : Type*) [Field K] [NumberField K] :
    Real.log ((differentIdeal ℤ (𝓞 K)).absNorm : ℝ) /
        (Module.finrank ℚ K : ℝ) =
      Real.log (NumberField.rootDiscr K) := by
  rw [log_rootDiscr_eq_log_abs_discr_div_finrank,
    NumberField.absNorm_differentIdeal K (𝓞 K)]
  congr 2
  rw [← Int.cast_abs, ← Int.cast_natCast, Int.natCast_natAbs]

/-- Degree-one fields have zero degree-normalized logarithmic different norm. -/
theorem log_absNorm_differentIdeal_div_finrank_eq_zero_of_finrank_one
    (K : Type*) [Field K] [NumberField K]
    (degree_one : Module.finrank ℚ K = 1) :
    Real.log ((differentIdeal ℤ (𝓞 K)).absNorm : ℝ) /
      (Module.finrank ℚ K : ℝ) = 0 := by
  rw [absNorm_differentIdeal_eq_one_of_finrank_one K degree_one]
  simp

/-- The degree-normalized logarithmic absolute discriminant vanishes over `ℚ`. -/
theorem rat_log_abs_discr_div_finrank_eq_zero :
    Real.log |(NumberField.discr ℚ : ℝ)| / (Module.finrank ℚ ℚ : ℝ) = 0 := by
  simp

/-- Equivalently, the logarithm of Mathlib's root discriminant vanishes over `ℚ`. -/
theorem rat_log_rootDiscr_eq_zero :
    Real.log (NumberField.rootDiscr ℚ) = 0 := by
  rw [NumberField.rootDiscr_rat, Real.log_one]

/-- The actual absolute different of `ℚ` contributes zero after logarithm and
degree normalization. This asserts only the arithmetic expression displayed. -/
theorem rat_log_absNorm_differentIdeal_div_finrank_eq_zero :
    Real.log ((differentIdeal ℤ (𝓞 ℚ)).absNorm : ℝ) /
      (Module.finrank ℚ ℚ : ℝ) = 0 := by
  exact log_absNorm_differentIdeal_div_finrank_eq_zero_of_finrank_one ℚ (by simp)

end IUT.ABCBridge.Arithmetic.RationalDifferent
