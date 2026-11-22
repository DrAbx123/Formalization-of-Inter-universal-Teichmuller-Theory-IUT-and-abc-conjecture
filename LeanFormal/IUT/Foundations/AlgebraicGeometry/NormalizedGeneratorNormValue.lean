import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedUniformizerImageGenerator
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionNormFormulaActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# Value of the normalized generator norm

The production formula module `Example36CompletionNormFormulaActual` records the
normalized log-norm formula as the exact missing comparison
`NormalizedLogNormComparison place`:

  `Real.log ‖x‖ = -((completionValuationExponent place x * log absNorm place) / d)`,

with `d = relativeCompletionDegree (k := ℚ) place`.

For the concrete place `d = 1` and `absNorm = 5`.  If the normalized image of
the actual uniformizer has valuation exponent `1`, the formula gives
`Real.log ‖image‖ = -log 5`, hence `‖image‖ = 1/5`.

This file proves that implication and transports it to the previous residuals
and to `CanonicalNormalizedNormEquality`.  The two inputs

* `NormalizedLogNormComparison concretePlace`;
* `completionValuationExponent concretePlace.maximalIdeal ux = 1`

are recorded as the exact residual; neither is postulated.

No fake norm value, no instance, no card.
-/

noncomputable section

namespace LeanFormal.IUT.NormalizedGeneratorNormValue

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.NormalizedUniformizerImageGenerator
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

local instance gaussianGeneratorNormValueIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

local instance factFivePrime : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The normalized completion. -/
abbrev normalizedCompletion : Type :=
  LeanFormal.IUT.NormalizedCompletion concretePlace

/-- The normalized image of the canonical uniformizer. -/
noncomputable abbrev normalizedUniformizerImage : normalizedCompletion :=
  LeanFormal.IUT.NormalizedUniformizerImageGenerator.normalizedUniformizerImage

/-- The normalized image as a unit. -/
noncomputable def normalizedUniformizerImageUnit : normalizedCompletionˣ :=
  Units.mk0 normalizedUniformizerImage (by
    exact LeanFormal.IUT.NormalizedUniformizerNormProof.normalizedUniformizerImage_ne_zero)

/-! ## Residuals -/

/-- The exact normalized log-norm formula at the concrete place. -/
def NormalizedLogNormResidual : Prop :=
  Example36.NormalizedLogNormComparison concretePlace

/-- The valuation exponent of the normalized uniformizer image is `1`. -/
def NormalizedGeneratorValuationResidual : Prop :=
  completionValuationExponent concretePlace.maximalIdeal
    normalizedUniformizerImageUnit = 1

/-! ## The arithmetic implication -/

theorem normalizedImage_norm_of_logNorm_and_valuation
    (hlog : NormalizedLogNormResidual)
    (hval : NormalizedGeneratorValuationResidual) :
    ‖normalizedUniformizerImage‖ = (5 : ℝ)⁻¹ :=
by
  have h := hlog normalizedUniformizerImageUnit
  have hval' : (completionValuationExponent concretePlace.maximalIdeal
      normalizedUniformizerImageUnit : ℤ) = 1 := hval
  rw [show (normalizedUniformizerImageUnit : normalizedCompletion) =
      normalizedUniformizerImage from rfl] at h
  rw [hval'] at h
  rw [concretePlace_upper_absNorm] at h
  rw [concreteGaussianFivePlace_relativeCompletionDegree_eq_one] at h
  norm_num at h
  have hpos : 0 < ‖normalizedUniformizerImage‖ :=
    norm_pos_iff.mpr LeanFormal.IUT.NormalizedUniformizerNormProof.normalizedUniformizerImage_ne_zero
  calc ‖normalizedUniformizerImage‖
      = Real.exp (Real.log ‖normalizedUniformizerImage‖) :=
        (Real.exp_log hpos).symm
    _ = Real.exp (-Real.log 5) := by rw [h]
    _ = (5 : ℝ)⁻¹ := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
        norm_num

theorem generatorNormResidual_of_logNorm_and_valuation
    (hlog : NormalizedLogNormResidual)
    (hval : NormalizedGeneratorValuationResidual) :
    NormalizedGeneratorNormResidual :=
  normalizedImage_norm_of_logNorm_and_valuation hlog hval

theorem normalizedUniformizerImageNormResidual_of_logNorm_and_valuation
    (hlog : NormalizedLogNormResidual)
    (hval : NormalizedGeneratorValuationResidual) :
    LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerImageNormResidual :=
  generatorNormResidual_of_logNorm_and_valuation hlog hval

theorem canonicalNormalizedNormEquality_of_logNorm_and_valuation
    (hlog : NormalizedLogNormResidual)
    (hval : NormalizedGeneratorValuationResidual) :
    CanonicalNormalizedNormEquality :=
  LeanFormal.IUT.NormalizedUniformizerImageGenerator.canonicalNormalizedNormEquality_of_generatorNorm
    (generatorNormResidual_of_logNorm_and_valuation hlog hval)

/-! ## Exact residual conjunction -/

/-- The exact remaining input: the normalized log-norm formula plus the
uniformizer image valuation exponent `1`.  Both are recorded, not inhabited. -/
def NormalizedGeneratorNormExactResidual : Prop :=
  NormalizedLogNormResidual ∧ NormalizedGeneratorValuationResidual

theorem generatorNormResidual_of_exactResidual
    (h : NormalizedGeneratorNormExactResidual) :
    NormalizedGeneratorNormResidual :=
  generatorNormResidual_of_logNorm_and_valuation h.1 h.2

theorem canonicalNormalizedNormEquality_of_exactResidual
    (h : NormalizedGeneratorNormExactResidual) :
    CanonicalNormalizedNormEquality :=
  canonicalNormalizedNormEquality_of_logNorm_and_valuation h.1 h.2

/-! ## Reduction to the production missing lemma -/

/-- The normalized log-norm residual is exactly the production missing lemma
`Example36.NormalizedLogNormComparison concretePlace`. -/
theorem normalizedLogNormResidual_iff :
    NormalizedLogNormResidual ↔
      Example36.NormalizedLogNormComparison concretePlace :=
  Iff.rfl

theorem exactResidual_iff :
    NormalizedGeneratorNormExactResidual ↔
      Example36.NormalizedLogNormComparison concretePlace ∧
        completionValuationExponent concretePlace.maximalIdeal
          normalizedUniformizerImageUnit = 1 :=
  Iff.rfl


/-! ## Auxiliary norm/log statements -/

theorem normalizedUniformizerImageUnit_coe :
    (normalizedUniformizerImageUnit : normalizedCompletion) =
      normalizedUniformizerImage :=
  rfl

theorem normalizedImage_norm_pos :
    0 < ‖normalizedUniformizerImage‖ :=
  norm_pos_iff.mpr LeanFormal.IUT.NormalizedUniformizerNormProof.normalizedUniformizerImage_ne_zero

theorem norm_eq_inv_five_of_log_eq_neg_log_five
    (h : Real.log ‖normalizedUniformizerImage‖ = -Real.log 5) :
    ‖normalizedUniformizerImage‖ = (5 : ℝ)⁻¹ :=
by
  calc ‖normalizedUniformizerImage‖
      = Real.exp (Real.log ‖normalizedUniformizerImage‖) :=
        (Real.exp_log normalizedImage_norm_pos).symm
    _ = Real.exp (-Real.log 5) := by rw [h]
    _ = (5 : ℝ)⁻¹ := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
        norm_num

theorem log_norm_of_logNorm_and_valuation
    (hlog : NormalizedLogNormResidual)
    (hval : NormalizedGeneratorValuationResidual) :
    Real.log ‖normalizedUniformizerImage‖ = -Real.log 5 :=
by
  have h := hlog normalizedUniformizerImageUnit
  rw [normalizedUniformizerImageUnit_coe, hval,
    concretePlace_upper_absNorm,
    concreteGaussianFivePlace_relativeCompletionDegree_eq_one] at h
  norm_num at h
  exact h

theorem normalizedImage_norm_of_logNorm_and_valuation'
    (hlog : NormalizedLogNormResidual)
    (hval : NormalizedGeneratorValuationResidual) :
    ‖normalizedUniformizerImage‖ = (5 : ℝ)⁻¹ :=
  norm_eq_inv_five_of_log_eq_neg_log_five
    (log_norm_of_logNorm_and_valuation hlog hval)

theorem normalizedGeneratorNormResidual_iff_norm_eq
    (h : ‖normalizedUniformizerImage‖ = (5 : ℝ)⁻¹) :
    NormalizedGeneratorNormResidual :=
  h

theorem normalizedImage_norm_ne_zero :
    ‖normalizedUniformizerImage‖ ≠ 0 :=
  ne_of_gt normalizedImage_norm_pos

theorem normalizedImage_norm_inv_of_exactResidual
    (h : NormalizedGeneratorNormExactResidual) :
    ‖normalizedUniformizerImage‖⁻¹ = 5 :=
by
  rw [normalizedImage_norm_of_logNorm_and_valuation h.1 h.2]
  norm_num
end LeanFormal.IUT.NormalizedGeneratorNormValue

end