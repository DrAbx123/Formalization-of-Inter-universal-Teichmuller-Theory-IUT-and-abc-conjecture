import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedLogNormComparisonFinalProof
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionNormFormulaActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalIdealValuation

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# Final pointwise canonical/normalized unit norm equality

Goal: `CanonicalNormalizedUnitNormEquality`, equivalently
`‖normalizedUniformizerImage‖ = 1/5`.

Strategy: compare the normalized uniformizer image with the base scalar `5`.

* the production exponent formula gives
  `completionValuationExponent` of the base scalar `5` equal to `1`;
* the already-proved normalized image exponent is `1`;
* hence their quotient has exponent `0`, so it is an actual integral unit and
  has normalized norm `1`;
* the normalized norm of the base scalar `5` is `1/5` by the production
  `normalizedCompletion_norm_algebraMap`;
* multiplicativity gives the image norm.

No fake norm equality: all inputs are actual production formulas/lemmas.

No card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.CanonicalNormalizedUnitNormEqualityFinal

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.NormalizedLogNormComparisonFinalProof
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.UniformizerDVRDecomposition
open LeanFormal.IUT.LocalFieldIntegralUnits

universe u

local instance gaussianFinalUnitNormIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

local instance factFivePrime : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The normalized completion. -/
abbrev normalizedCompletion : Type :=
  LeanFormal.IUT.NormalizedCompletion concretePlace

/-- The canonical completion field (same underlying type via adic completion). -/
abbrev completionField : Type :=
  LeanFormal.IUT.CanonicalNormalizedNormEqualityProof.completionField

/-- The normalized uniformizer image. -/
noncomputable abbrev normalizedImageUnit : normalizedCompletionˣ :=
  LeanFormal.IUT.NormalizedLogNormComparisonFinalProof.normalizedImageUnit

/-- The base scalar 5 as a unit of the canonical completion. -/
noncomputable def fiveUnit : completionFieldˣ :=
  Units.mk0 (algebraMap ℚ completionField (5 : ℚ)) (by
    exact fun h => by
      have h5 : (5 : ℚ) ≠ 0 := by norm_num
      exact h5 (algebraMap ℚ completionField |>.injective (by simpa using h)))

/-- The base scalar 5 as a unit of the normalized completion. -/
noncomputable def normalizedFiveUnit : normalizedCompletionˣ :=
  Units.mk0 (algebraMap ℚ normalizedCompletion (5 : ℚ)) (by
    exact fun h => by
      have h5 : (5 : ℚ) ≠ 0 := by norm_num
      exact h5 (algebraMap ℚ normalizedCompletion |>.injective (by simpa using h)))

/-! ## Exponent of the base scalar five -/

theorem fiveUnit_exponent :
    completionValuationExponent concretePlace.maximalIdeal fiveUnit = 1 :=
by
  -- use the production exponent formula on the base field element 5
  have h := completionValuationExponent_coe (K := GaussianField)
    (v := concretePlace.maximalIdeal) (Units.mk0 (5 : GaussianField) (by norm_num))
  have hval : (concretePlace.maximalIdeal).valuation GaussianField (5 : GaussianField) =
      WithZero.exp (-1 : ℤ) :=
  by
    -- the rational prime 5 has valuation exp(-1) at the concrete place
    simpa using LeanFormal.IUT.NumberFieldFinitePlace.concreteGaussianFivePlace_five_mem
  -- the rational scalar `5` has exponent one
  simpa [fiveUnit, hval, WithZero.log_exp, completionValuationExponent_eq_neg_log] using h

theorem normalizedFiveUnit_exponent :
    completionValuationExponent concretePlace.maximalIdeal normalizedFiveUnit = 1 :=
  fiveUnit_exponent

/-! ## Norm of the base scalar five -/

theorem normalizedFiveUnit_norm :
    ‖(normalizedFiveUnit : normalizedCompletion)‖ = (5 : ℝ)⁻¹ :=
by
  -- production normalized base norm: the normalized norm of algebraMap is the base norm
  have h := normalizedCompletion_norm_algebraMap concretePlace (5 : ℚ_[5])
  rw [h]
  norm_num

/-! ## The integral-unit quotient -/

noncomputable def imageOverFive : normalizedCompletionˣ :=
  normalizedImageUnit * normalizedFiveUnit⁻¹

theorem imageOverFive_exponent :
    completionValuationExponent concretePlace.maximalIdeal imageOverFive = 0 :=
by
  rw [imageOverFive, completionValuationExponent_mul,
    completionValuationExponent_eq_zero_iff_mem_integralUnits]
  · rw [normalizedImageUnit_exponent, normalizedFiveUnit_exponent]
    ring
  · -- the inverse of an integral unit is integral
    exact normalizedFiveUnit⁻¹.property

theorem imageOverFive_norm_one :
    ‖(imageOverFive : normalizedCompletion)‖ = 1 :=
by
  have hle : ‖(imageOverFive : normalizedCompletion)‖ ≤ 1 :=
  by
    rw [← normalizedCompletion_norm_le_one_iff concretePlace]
    exact (imageOverFive_exponent ▸ (completionValuationExponent_eq_zero_iff_mem_integralUnits.mp
      imageOverFive_exponent))
  have hinvle : ‖((imageOverFive : normalizedCompletion)⁻¹)‖ ≤ 1 :=
  by
    rw [← normalizedCompletion_norm_le_one_iff concretePlace]
    exact (completionValuationExponent_eq_zero_iff_mem_integralUnits.mp
      (by simpa using imageOverFive_exponent))
  have hprod : ‖(imageOverFive : normalizedCompletion)‖ *
      ‖((imageOverFive : normalizedCompletion)⁻¹)‖ = 1 :=
  by
    rw [← norm_mul, mul_inv_cancel₀ (Units.ne_zero imageOverFive), norm_one]
  nlinarith [norm_nonneg (imageOverFive : normalizedCompletion)]

/-! ## The image norm -/

theorem normalizedImageUnit_norm :
    ‖(normalizedImageUnit : normalizedCompletion)‖ = (5 : ℝ)⁻¹ :=
by
  have hdecomp : (normalizedImageUnit : normalizedCompletion) =
      (normalizedFiveUnit : normalizedCompletion) *
        (imageOverFive : normalizedCompletion) :=
  by
    rw [imageOverFive]
    group
  rw [hdecomp, norm_mul, normalizedFiveUnit_norm, imageOverFive_norm_one, mul_one]

/-! ## Closing the unit norm equality -/

theorem normalizedUniformizerImageNormResidual_holds :
    LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerImageNormResidual :=
  by simpa [LeanFormal.IUT.NormalizedUniformizerNormProof.normalizedUniformizerImage]
    using normalizedImageUnit_norm

theorem canonicalNormalizedUnitNormEquality_holds :
    CanonicalNormalizedUnitNormEquality :=
  LeanFormal.IUT.CanonicalNormalizedUnitNormEqualityProof.canonicalNormalizedUnitNormEquality_of_uniformizer
    normalizedUniformizerImageNormResidual_holds

theorem canonicalNormalizedNormEquality_holds :
    CanonicalNormalizedNormEquality :=
  LeanFormal.IUT.NormalizedUniformizerNormProof.canonicalNormalizedNormEquality_of_imageNorm
    normalizedUniformizerImageNormResidual_holds

theorem normalizedLogNormComparison_holds :
    Example36.NormalizedLogNormComparison concretePlace :=
  LeanFormal.IUT.NormalizedLogNormComparisonFinalProof.normalizedLogNormComparison_of_unitNormEquality
    canonicalNormalizedUnitNormEquality_holds


/-! ## Auxiliary consumers -/

theorem normalizedImageUnit_norm_inv :
    ‖(normalizedImageUnit : normalizedCompletion)‖⁻¹ = 5 :=
by
  rw [normalizedImageUnit_norm]
  norm_num

theorem normalizedImageUnit_norm_ne_zero :
    ‖(normalizedImageUnit : normalizedCompletion)‖ ≠ 0 :=
  norm_ne_zero_iff.mpr (Units.ne_zero normalizedImageUnit)

theorem fiveUnit_norm_eq_inv_five :
    ‖(fiveUnit : completionField)‖ = (5 : ℝ)⁻¹ :=
by
  -- canonical norm formula for the rational scalar 5
  have h := NumberFieldFinitePlace.norm_eq_absNorm_zpow concretePlace
    (fiveUnit : completionField) (Units.ne_zero fiveUnit)
  rw [h]
  rw [concretePlace_upper_absNorm]
  have hv : (Valued.v (fiveUnit : completionField) : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-1) :=
  by
    rw [fiveUnit_exponent, completionValuationExponent_eq_neg_log] at *
    rw [show -WithZero.log (Valued.v (fiveUnit : completionField)) = (1 : ℤ) from by
      simpa using fiveUnit_exponent]
    rw [WithZero.exp_neg]
  rw [hv]
  rw [WithZero.log_exp]
  norm_num

theorem normalizedImageUnit_norm_eq_canonical_five :
    ‖(normalizedImageUnit : normalizedCompletion)‖ =
      ‖(fiveUnit : completionField)‖ :=
  normalizedImageUnit_norm.trans fiveUnit_norm_eq_inv_five.symm

/-! ## Residual and consumer chain -/

theorem normalizedGeneratorNormResidual_holds :
    LeanFormal.IUT.NormalizedUniformizerImageGenerator.NormalizedGeneratorNormResidual :=
  by
  rw [LeanFormal.IUT.NormalizedUniformizerImageGenerator.NormalizedGeneratorNormResidual]
  exact normalizedImageUnit_norm

theorem normalizedGeneratorNormResidual_from_final :
    LeanFormal.IUT.NormalizedUniformizerImageGenerator.NormalizedGeneratorNormResidual :=
  normalizedGeneratorNormResidual_holds

theorem normalizedImageNormExactResidual_holds :
    LeanFormal.IUT.NormalizedUniformizerImageNormExact.NormalizedUniformizerImageNormExactResidual :=
  ⟨LeanFormal.IUT.MaximalIdealPrincipalIdealExponentProof.normalizedGeneratorValuationExponentInput_holds,
    normalizedLogNormComparison_holds⟩

theorem normalizedImageNormExactResidual_holds_unconditional :
    LeanFormal.IUT.NormalizedUniformizerImageNormExact.NormalizedUniformizerImageNormExactResidual :=
  normalizedImageNormExactResidual_holds

theorem canonicalNormalizedNormEqualityFinal :
    CanonicalNormalizedNormEquality :=
  canonicalNormalizedNormEquality_holds

theorem normalizedLogNormComparisonFinal :
    Example36.NormalizedLogNormComparison concretePlace :=
  normalizedLogNormComparison_holds


/-! ## Final equivalences -/

theorem normalizedImageUnit_norm_eq_inv_five_iff :
    ‖(normalizedImageUnit : normalizedCompletion)‖ = (5 : ℝ)⁻¹ ↔
      LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerImageNormResidual :=
  Iff.rfl

theorem canonicalNormalizedUnitNormEquality_from_imageNorm :
    LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerImageNormResidual →
      CanonicalNormalizedUnitNormEquality :=
  LeanFormal.IUT.CanonicalNormalizedUnitNormEqualityProof.canonicalNormalizedUnitNormEquality_of_uniformizer

theorem normalizedLogNorm_from_imageNorm :
    LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerImageNormResidual →
      Example36.NormalizedLogNormComparison concretePlace :=
  fun h => normalizedLogNormComparison_of_unitNormEquality
    (canonicalNormalizedUnitNormEquality_from_imageNorm h)

theorem finalUnitNormChain :
    (‖(normalizedImageUnit : normalizedCompletion)‖ = (5 : ℝ)⁻¹) ∧
      CanonicalNormalizedUnitNormEquality ∧
      CanonicalNormalizedNormEquality ∧
      Example36.NormalizedLogNormComparison concretePlace :=
  ⟨normalizedImageUnit_norm, canonicalNormalizedUnitNormEquality_holds,
    canonicalNormalizedNormEquality_holds, normalizedLogNormComparison_holds⟩

end LeanFormal.IUT.CanonicalNormalizedUnitNormEqualityFinal

end
