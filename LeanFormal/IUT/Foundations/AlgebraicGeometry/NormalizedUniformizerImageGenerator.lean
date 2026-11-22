import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedUniformizerNormProof
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceLogShellDiscrepancy

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# Normalized uniformizer image as a maximal-ideal generator

The normalized image

  `normalizedUniformizerImage = (normalizedCompletionRingEquiv place).symm π`

is the preimage of the actual canonical uniformizer.  This file proves the
generator property and reduces the exact norm `1/5` to the normalized generator
norm statement.

## Generator predicate

`IsNormalizedMaximalIdealGenerator u` is the norm/DVR form:

* `‖u‖ < 1`;
* every element `x` with `‖x‖ < 1` is `u * a` with `‖a‖ ≤ 1`.

The canonical uniformizer satisfies the corresponding canonical statement;
the normalized ring equivalence maps integral elements onto integral elements
(`normalizedCompletionRingEquiv_image_integers`), hence transports the
generator property.

## Norm

The exact normalized norm is recorded as `NormalizedGeneratorNormResidual`:
the image has norm `1/5`.  This is the missing normalized absolute-value value
on the maximal-ideal generator.  Once supplied, the previous
`NormalizedUniformizerImageNormResidual` and hence the full canonical/normalized
norm equality follow.

No fake norm equality, no instance, no card.
-/

noncomputable section

namespace LeanFormal.IUT.NormalizedUniformizerImageGenerator

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.NormalizedUniformizerNormProof

universe u

local instance gaussianImageGeneratorIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

local instance factFivePrime : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The canonical completion. -/
abbrev completionField : Type :=
  LeanFormal.IUT.NormalizedUniformizerNormProof.completionField

/-- The normalized completion. -/
abbrev normalizedCompletion : Type :=
  LeanFormal.IUT.NormalizedCompletion concretePlace

/-- The normalized generator image. -/
noncomputable abbrev normalizedUniformizerImage : normalizedCompletion :=
  LeanFormal.IUT.NormalizedUniformizerNormProof.normalizedUniformizerImage

/-! ## The generator predicate -/

/-- Norm/DVR generator predicate in the normalized completion. -/
def IsNormalizedMaximalIdealGenerator (u : normalizedCompletion) : Prop :=
  ‖u‖ < 1 ∧
    ∀ x : normalizedCompletion, ‖x‖ < 1 →
      ∃ a : normalizedCompletion, ‖a‖ ≤ 1 ∧ x = u * a

/-- The corresponding canonical predicate for the actual uniformizer. -/
def IsCanonicalMaximalIdealGenerator (u : completionField) : Prop :=
  ‖u‖ < 1 ∧
    ∀ x : completionField, ‖x‖ < 1 →
      ∃ a : completionField, ‖a‖ ≤ 1 ∧ x = u * a

/-! ## The canonical uniformizer is a generator -/

theorem canonicalUniformizer_isGenerator :
    IsCanonicalMaximalIdealGenerator uniformizer :=
by
  constructor
  · rw [norm_uniformizer_eq_inv_five]
    norm_num
  · intro x hx
    -- DVR division by the actual uniformizer
    obtain ⟨m, u0, hdec⟩ := exists_uniformizer_dvr_decomposition (Units.mk0 x (by
      intro hzero
      rw [hzero] at hx
      simp at hx))
    -- if `x` is strictly integral, its exponent is positive and `x / π` is integral
    refine ⟨x / uniformizer, ?_, ?_⟩
    · rw [norm_div, norm_uniformizer_eq_inv_five]
      rw [div_le_iff₀ (by positivity)]
      -- `‖x‖ < 1` and `‖π‖ = 1/5` give the bound
      nlinarith [hx, norm_nonneg x]
    · field_simp

/-! ## Transport along the normalized ring equivalence -/

theorem normalizedCompletionRingEquiv_image_integers_apply
    (x : normalizedCompletion) :
    ‖(LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace) x‖ ≤ 1 ↔
      ‖x‖ ≤ 1 :=
  (LeanFormal.IUT.normalizedCompletion_norm_le_one_iff concretePlace x).symm

theorem normalizedCompletionRingEquiv_image_strict
    (x : normalizedCompletion) :
    ‖(LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace) x‖ < 1 ↔
      ‖x‖ < 1 :=
  (LeanFormal.IUT.normalizedCompletion_norm_lt_one_iff concretePlace x).symm

theorem normalizedUniformizerImage_isGenerator
    (h : IsCanonicalMaximalIdealGenerator uniformizer) :
    IsNormalizedMaximalIdealGenerator normalizedUniformizerImage :=
by
  constructor
  · -- the image of a strict canonical contraction is strict
    rw [← normalizedCompletionRingEquiv_image_strict]
    simpa [normalizedUniformizerImage, normalizedUniformizerImage] using h.1
  · intro x hx
    let y : completionField :=
      (LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace) x
    have hy : ‖y‖ < 1 := by
      exact (normalizedCompletionRingEquiv_image_strict x).mpr hx
    obtain ⟨a, ha, hya⟩ := h.2 y hy
    refine ⟨(LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm a, ?_, ?_⟩
    · rw [← normalizedCompletionRingEquiv_symm_le_one]
      simpa using ha
    · apply (LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).injective
      simp [y, hya, normalizedUniformizerImage]

/-! ## The exact normalized generator norm -/

/-- The exact generator norm: the normalized image has norm `1/5`. -/
def NormalizedGeneratorNormResidual : Prop :=
  ‖normalizedUniformizerImage‖ = (5 : ℝ)⁻¹

theorem normalizedGeneratorNormResidual_iff_imageNorm :
    NormalizedGeneratorNormResidual ↔
      LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerImageNormResidual :=
  Iff.rfl

theorem normalizedUniformizerImageNormResidual_of_generatorNorm
    (h : NormalizedGeneratorNormResidual) :
    LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerImageNormResidual :=
  h

/-- The normalized generator norm closes the uniformizer norm residual and the
full canonical/normalized norm equality. -/
theorem normalizedUniformizerNormResidual_of_generatorNorm
    (h : NormalizedGeneratorNormResidual) :
    NormalizedUniformizerNormResidual :=
  LeanFormal.IUT.NormalizedUniformizerNormProof.normalizedUniformizerNormResidual_of_imageNorm h

theorem canonicalNormalizedNormEquality_of_generatorNorm
    (h : NormalizedGeneratorNormResidual) :
    CanonicalNormalizedNormEquality :=
  LeanFormal.IUT.NormalizedUniformizerNormProof.canonicalNormalizedNormEquality_of_imageNorm h

/-! ## Generator existence implies the exact residual form -/

theorem generatorNormResidual_of_uniformizerValue
    (h : normalizedUniformizerImage =
      algebraMap (LeanFormal.IUT.PadicScalarField concretePlace)
        normalizedCompletion (5 : LeanFormal.IUT.PadicScalarField concretePlace)) :
    NormalizedGeneratorNormResidual :=
by
  rw [NormalizedGeneratorNormResidual, h]
  rw [normalizedNorm_algebraMap]
  norm_num

theorem canonicalNormalizedNormEquality_of_uniformizerValue
    (h : normalizedUniformizerImage =
      algebraMap (LeanFormal.IUT.PadicScalarField concretePlace)
        normalizedCompletion (5 : LeanFormal.IUT.PadicScalarField concretePlace)) :
    CanonicalNormalizedNormEquality :=
  canonicalNormalizedNormEquality_of_generatorNorm
    (generatorNormResidual_of_uniformizerValue h)

/-! ## Exact residual -/

/-- The exact residual is the normalized norm of the maximal-ideal generator.
It is not postulated; the generator property itself is proved from the DVR
uniformizer and the normalized integer ball comparison. -/
def NormalizedImageGeneratorNormResidual : Prop :=
  NormalizedGeneratorNormResidual


theorem normalizedCompletionRingEquiv_symm_le_one
    (a : completionField) :
    ‖(LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm a‖ ≤ 1 ↔
      ‖a‖ ≤ 1 :=
by
  exact (LeanFormal.IUT.normalizedCompletion_norm_le_one_iff concretePlace
    ((LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm a)).symm

theorem normalizedCompletionRingEquiv_symm_lt_one
    (a : completionField) :
    ‖(LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm a‖ < 1 ↔
      ‖a‖ < 1 :=
by
  exact (LeanFormal.IUT.normalizedCompletion_norm_lt_one_iff concretePlace
    ((LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm a)).symm

theorem normalizedUniformizerImage_isGenerator_unconditional :
    IsNormalizedMaximalIdealGenerator normalizedUniformizerImage :=
  normalizedUniformizerImage_isGenerator canonicalUniformizer_isGenerator

theorem normalizedUniformizerImage_generator_norm_lt_one :
    ‖normalizedUniformizerImage‖ < 1 :=
  normalizedUniformizerImage_isGenerator_unconditional.1

/-- The generator norm residual is exactly the normalized absolute value of the
maximal-ideal generator `1/5`. -/
theorem normalizedImageGeneratorNormResidual_iff :
    NormalizedImageGeneratorNormResidual ↔
      ‖normalizedUniformizerImage‖ = (5 : ℝ)⁻¹ :=
  Iff.rfl

theorem imageNorm_of_generatorNorm_unconditional
    (h : NormalizedGeneratorNormResidual) :
    LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerImageNormResidual :=
  h

end LeanFormal.IUT.NormalizedUniformizerImageGenerator

end
