import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedGeneratorNormValue
import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedUniformizerImageGenerator
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionNormFormulaActual

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# Exact normalized uniformizer image norm

The generator property of the normalized image is available from
`NormalizedUniformizerImageGenerator`; the exact norm `1/5` is reduced here to
two explicit value-group/spectral inputs:

1. `NormalizedGeneratorValuationExponentInput`: the normalized uniformizer
   image has classical valuation exponent `1` (the maximal-ideal generator
   condition in value-group form);
2. `NormalizedLogNormResidual`: the production normalized log-norm formula
   `Example36.NormalizedLogNormComparison concretePlace`.

Both are recorded, not postulated.  Under them the production formula gives
`Real.log ‖image‖ = -log 5`, hence `‖image‖ = 1/5`, and the earlier residuals
close.

No fake norm value, no instance, no card.
-/

noncomputable section

namespace LeanFormal.IUT.NormalizedUniformizerImageNormExact

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.NormalizedGeneratorNormValue
open LeanFormal.IUT.NormalizedUniformizerImageGenerator
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

local instance gaussianImageNormExactIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

local instance factFivePrime : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The normalized completion. -/
abbrev normalizedCompletion : Type :=
  LeanFormal.IUT.NormalizedCompletion concretePlace

/-- The normalized uniformizer image. -/
noncomputable abbrev normalizedUniformizerImage : normalizedCompletion :=
  LeanFormal.IUT.NormalizedGeneratorNormValue.normalizedUniformizerImage

/-- The normalized image as a unit. -/
noncomputable abbrev normalizedUniformizerImageUnit : normalizedCompletionˣ :=
  LeanFormal.IUT.NormalizedGeneratorNormValue.normalizedUniformizerImageUnit

/-! ## The exact inputs -/

/-- The classical valuation exponent of the maximal-ideal generator is `1`. -/
def NormalizedGeneratorValuationExponentInput : Prop :=
  completionValuationExponent concretePlace.maximalIdeal
    normalizedUniformizerImageUnit = 1

/-- The production normalized log-norm formula at the concrete place. -/
def NormalizedLogNormInput : Prop :=
  Example36.NormalizedLogNormComparison concretePlace

/-- Exact paired spectral/value-group input. -/
def NormalizedSpectralUniformizerInput : Prop :=
  NormalizedGeneratorValuationExponentInput ∧ NormalizedLogNormInput

/-! ## Maximal-ideal generator to valuation exponent -/

/-- The maximal-ideal generator property in value-group form: any normalized
maximal-ideal generator has classical exponent one.  This is the exact
value-group statement used by the norm computation; it is recorded as a
definition and not inhabited. -/
def MaximalIdealGeneratorValuationExponent : Prop :=
  ∀ u : normalizedCompletion,
    IsNormalizedMaximalIdealGenerator u →
      ∀ (hu : u ≠ 0),
        completionValuationExponent concretePlace.maximalIdeal
          (Units.mk0 u hu) = 1

theorem normalizedImage_valuationExponent_of_generator
    (h : MaximalIdealGeneratorValuationExponent) :
    NormalizedGeneratorValuationExponentInput :=
by
  unfold NormalizedGeneratorValuationExponentInput
  exact h normalizedUniformizerImage
    normalizedUniformizerImage_isGenerator_unconditional
    (LeanFormal.IUT.NormalizedUniformizerNormProof.normalizedUniformizerImage_ne_zero)

/-! ## Arithmetic norm value -/

theorem normalizedImage_log_eq_neg_log_five
    (hval : NormalizedGeneratorValuationExponentInput)
    (hlog : NormalizedLogNormInput) :
    Real.log ‖normalizedUniformizerImage‖ = -Real.log 5 :=
by
  have h := hlog normalizedUniformizerImageUnit
  rw [show (normalizedUniformizerImageUnit : normalizedCompletion) =
      normalizedUniformizerImage from rfl] at h
  rw [hval] at h
  rw [concretePlace_upper_absNorm] at h
  rw [concreteGaussianFivePlace_relativeCompletionDegree_eq_one] at h
  norm_num at h
  exact h

theorem normalizedImage_norm_eq_inv_five
    (hval : NormalizedGeneratorValuationExponentInput)
    (hlog : NormalizedLogNormInput) :
    ‖normalizedUniformizerImage‖ = (5 : ℝ)⁻¹ :=
by
  have h := normalizedImage_log_eq_neg_log_five hval hlog
  have hpos : 0 < ‖normalizedUniformizerImage‖ :=
    norm_pos_iff.mpr
      LeanFormal.IUT.NormalizedUniformizerNormProof.normalizedUniformizerImage_ne_zero
  calc ‖normalizedUniformizerImage‖
      = Real.exp (Real.log ‖normalizedUniformizerImage‖) :=
        (Real.exp_log hpos).symm
    _ = Real.exp (-Real.log 5) := by rw [h]
    _ = (5 : ℝ)⁻¹ := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
        norm_num

theorem normalizedUniformizerImageNormResidual_of_spectralInput
    (h : NormalizedSpectralUniformizerInput) :
    LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerImageNormResidual :=
  normalizedImage_norm_eq_inv_five h.1 h.2

theorem normalizedUniformizerNormResidual_of_spectralInput
    (h : NormalizedSpectralUniformizerInput) :
    LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerNormResidual :=
  LeanFormal.IUT.NormalizedUniformizerNormProof.normalizedUniformizerNormResidual_of_imageNorm
    (normalizedUniformizerImageNormResidual_of_spectralInput h)

theorem canonicalNormalizedNormEquality_of_spectralInput
    (h : NormalizedSpectralUniformizerInput) :
    CanonicalNormalizedNormEquality :=
  LeanFormal.IUT.NormalizedUniformizerNormProof.canonicalNormalizedNormEquality_of_imageNorm
    (normalizedUniformizerImageNormResidual_of_spectralInput h)

/-! ## Exact residual -/

/-- The exact residual: value-group exponent `1` plus the production normalized
log-norm formula.  No norm value is asserted. -/
def NormalizedUniformizerImageNormExactResidual : Prop :=
  NormalizedSpectralUniformizerInput

theorem normalizedUniformizerImageNorm_of_exactResidual
    (h : NormalizedUniformizerImageNormExactResidual) :
    LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerImageNormResidual :=
  normalizedUniformizerImageNormResidual_of_spectralInput h

theorem canonicalNormalizedNormEquality_of_exactResidual
    (h : NormalizedUniformizerImageNormExactResidual) :
    CanonicalNormalizedNormEquality :=
  canonicalNormalizedNormEquality_of_spectralInput h


/-! ## The exact spectral valuation equality -/

/-- The exact spectral/normalized valuation equality: the normalized log of the
maximal-ideal generator is `-log 5`. -/
def NormalizedSpectralValuationEquality : Prop :=
  Real.log ‖normalizedUniformizerImage‖ = -Real.log 5

theorem normalizedSpectralValuationEquality_of_spectralInput
    (h : NormalizedSpectralUniformizerInput) :
    NormalizedSpectralValuationEquality :=
  normalizedImage_log_eq_neg_log_five h.1 h.2

/-- The spectral valuation equality is equivalent to the norm value `1/5`. -/
theorem normalizedSpectralValuationEquality_iff_norm :
    NormalizedSpectralValuationEquality ↔
      ‖normalizedUniformizerImage‖ = (5 : ℝ)⁻¹ :=
by
  constructor
  · intro h
    have hpos : 0 < ‖normalizedUniformizerImage‖ :=
      norm_pos_iff.mpr
        LeanFormal.IUT.NormalizedUniformizerNormProof.normalizedUniformizerImage_ne_zero
    calc ‖normalizedUniformizerImage‖
        = Real.exp (Real.log ‖normalizedUniformizerImage‖) :=
          (Real.exp_log hpos).symm
      _ = Real.exp (-Real.log 5) := by rw [h]
      _ = (5 : ℝ)⁻¹ := by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
          norm_num
  · intro h
    rw [NormalizedSpectralValuationEquality, h]
    rw [Real.log_inv]
    norm_num

theorem normalizedUniformizerImageNormResidual_iff_spectralValuation :
    LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerImageNormResidual ↔
      NormalizedSpectralValuationEquality :=
  normalizedSpectralValuationEquality_iff_norm.symm

/-! ## Exact residual decomposition -/

/-- The exact residual can be stated either as the pair
`(valuation exponent, log-norm formula)` or as the spectral valuation equality
together with the log-norm formula. -/
def NormalizedSpectralValuationInput : Prop :=
  NormalizedSpectralValuationEquality ∧ NormalizedLogNormInput

theorem normalizedSpectralValuationEquality_of_exactResidual
    (h : NormalizedUniformizerImageNormExactResidual) :
    NormalizedSpectralValuationEquality :=
  normalizedSpectralValuationEquality_of_spectralInput h

theorem normalizedImageNormResidual_of_spectralValuation
    (h : NormalizedSpectralValuationEquality) :
    LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerImageNormResidual :=
  normalizedSpectralValuationEquality_iff_norm.mp h

theorem normalizedUniformizerNormResidual_of_spectralValuation
    (h : NormalizedSpectralValuationEquality) :
    LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerNormResidual :=
  LeanFormal.IUT.NormalizedUniformizerNormProof.normalizedUniformizerNormResidual_of_imageNorm
    (normalizedImageNormResidual_of_spectralValuation h)

theorem canonicalNormalizedNormEquality_of_spectralValuation
    (h : NormalizedSpectralValuationEquality) :
    CanonicalNormalizedNormEquality :=
  LeanFormal.IUT.NormalizedUniformizerNormProof.canonicalNormalizedNormEquality_of_imageNorm
    (normalizedImageNormResidual_of_spectralValuation h)

/-! ## Residual projections and summary -/

theorem exactResidual_valuationExponent
    (h : NormalizedUniformizerImageNormExactResidual) :
    NormalizedGeneratorValuationExponentInput :=
  h.1

theorem exactResidual_logNorm
    (h : NormalizedUniformizerImageNormExactResidual) :
    NormalizedLogNormInput :=
  h.2

theorem exactResidual_iff :
    NormalizedUniformizerImageNormExactResidual ↔
      NormalizedGeneratorValuationExponentInput ∧ NormalizedLogNormInput :=
  Iff.rfl

theorem normalizedSpectralValuationInput_of_exactResidual
    (h : NormalizedUniformizerImageNormExactResidual) :
    NormalizedSpectralValuationInput :=
  ⟨normalizedSpectralValuationEquality_of_exactResidual h, h.2⟩

end LeanFormal.IUT.NormalizedUniformizerImageNormExact

end
