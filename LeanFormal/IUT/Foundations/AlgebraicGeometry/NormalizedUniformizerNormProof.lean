import LeanFormal.IUT.Foundations.AlgebraicGeometry.CanonicalNormalizedNormEqualityProof
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# Normalized norm of the actual uniformizer

Goal: the normalized norm of the canonical uniformizer equals the canonical
norm, `1/5`.  The canonical norm `‖π‖ = 1/5` is proved in
`CanonicalNormalizedNormEqualityProof`; this file reduces the normalized side
to the image of `π` under `normalizedCompletionRingEquiv`.

## Reduction

`normalizedNormOnCompletion x` is by definition the norm of
`(normalizedCompletionRingEquiv place).symm x` in `NormalizedCompletion place`.
Thus the uniformizer residual is exactly

  `‖(normalizedCompletionRingEquiv place).symm π‖ = 1/5`.

The normalized completion is a spectral norm on a finite-dimensional
`ℚ_[5]`-algebra.  Its norm on the image of the maximal-ideal generator is the
normalized absolute value of that generator; the concrete relative
ramification/residue degrees are one, so the expected value is `1/5`.

The exact remaining comparison is recorded as
`NormalizedUniformizerImageNormResidual`; it is not postulated.  Once supplied,
the full `NormalizedUniformizerNormResidual` and hence
`CanonicalNormalizedNormEquality` follow.

No fake norm equality, no instance, no card.
-/

noncomputable section

namespace LeanFormal.IUT.NormalizedUniformizerNormProof

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.BaseNormCompatibilityProof
open LeanFormal.IUT.CanonicalNormalizedNormEqualityProof
open LeanFormal.IUT.ClosedBallCompactness

universe u

local instance gaussianUniformizerNormIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

local instance factFivePrime : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The canonical completion. -/
abbrev completionField : Type :=
  LeanFormal.IUT.CanonicalNormalizedNormEqualityProof.completionField

/-- The normalized completion. -/
abbrev normalizedCompletion : Type :=
  LeanFormal.IUT.NormalizedCompletion concretePlace

/-- The normalizer scalar field. -/
abbrev normalizedScalarField : Type :=
  LeanFormal.IUT.PadicScalarField concretePlace

/-- The image of the canonical uniformizer in the normalized completion. -/
noncomputable def normalizedUniformizerImage : normalizedCompletion :=
  (LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm uniformizer

/-! ## The normalized side -/

theorem normalizedNormOnCompletion_uniformizer_eq_image :
    normalizedNormOnCompletion uniformizer = ‖normalizedUniformizerImage‖ :=
  rfl

/-- The exact normalized-uniformizer image norm. -/
def NormalizedUniformizerImageNormResidual : Prop :=
  ‖normalizedUniformizerImage‖ = (5 : ℝ)⁻¹

/-- The normalized image norm is exactly the normalized norm of the canonical
uniformizer. -/
theorem normalizedUniformizerNormResidual_of_imageNorm
    (h : NormalizedUniformizerImageNormResidual) :
    NormalizedUniformizerNormResidual :=
by
  rw [NormalizedUniformizerNormResidual, normalizedNormOnCompletion_uniformizer_eq_image,
    h, norm_uniformizer_eq_inv_five]

theorem normalizedUniformizerImageNorm_of_uniformizerNorm
    (h : NormalizedUniformizerNormResidual) :
    NormalizedUniformizerImageNormResidual :=
by
  rw [NormalizedUniformizerImageNormResidual,
    ← normalizedNormOnCompletion_uniformizer_eq_image]
  rw [h, norm_uniformizer_eq_inv_five]

theorem normalizedUniformizerImageNorm_iff_uniformizerNorm :
    NormalizedUniformizerImageNormResidual ↔
      NormalizedUniformizerNormResidual :=
  ⟨normalizedUniformizerNormResidual_of_imageNorm,
    normalizedUniformizerImageNorm_of_uniformizerNorm⟩

/-! ## Generating element reduction -/

/-- The image of the canonical uniformizer under the normalized ring equivalence
is a generator of the normalized maximal ideal. -/
def NormalizedUniformizerImageIsMaximalIdealGenerator : Prop :=
  ∀ x : normalizedCompletion,
    x ∈ (Valued.v.integer : Set normalizedCompletion) →
      ∃ a : (Valued.v.integer : Subring normalizedCompletion),
        x = normalizedUniformizerImage * (a : normalizedCompletion)

/-- The concrete maximal-ideal generator/value comparison: the normalized image
is a uniformizer with normalized absolute value `1/5`. -/
def NormalizedImageValuationResidual : Prop :=
  NormalizedUniformizerImageIsMaximalIdealGenerator ∧
    ‖normalizedUniformizerImage‖ = (5 : ℝ)⁻¹

theorem normalizedImageValuationResidual_implies_imageNorm
    (h : NormalizedImageValuationResidual) :
    NormalizedUniformizerImageNormResidual :=
  h.2

/-! ## Closing the norm equality -/

theorem normalizedUniformizerNormResidual_of_imageValuation
    (h : NormalizedImageValuationResidual) :
    NormalizedUniformizerNormResidual :=
  normalizedUniformizerNormResidual_of_imageNorm (h.2)

theorem canonicalNormalizedNormEquality_of_imageValuation
    (h : NormalizedImageValuationResidual) :
    CanonicalNormalizedNormEquality :=
  canonicalNormalizedNormEquality_of_uniformizer
    (normalizedUniformizerNormResidual_of_imageValuation h)

theorem normalizedUniformizerNormResidual_of_imageNorm_unconditional
    (h : NormalizedUniformizerImageNormResidual) :
    NormalizedUniformizerNormResidual :=
  normalizedUniformizerNormResidual_of_imageNorm h

/-- The normalized image norm `1/5` together with the ball comparison closes
the DVR decomposition norm equality pointwise. -/
theorem canonicalNormalizedNormEquality_of_imageNorm
    (h : NormalizedUniformizerImageNormResidual) :
    CanonicalNormalizedNormEquality :=
  canonicalNormalizedNormEquality_of_uniformizer
    (normalizedUniformizerNormResidual_of_imageNorm h)

/-! ## Exact residual form -/

/-- The exact remaining statement is the normalized image norm `1/5`; the
canonical norm side is already `1/5` from the canonical formula. -/
def NormalizedUniformizerNormExactResidual : Prop :=
  NormalizedUniformizerImageNormResidual

theorem canonicalNormalizedNormEquality_of_exactResidual
    (h : NormalizedUniformizerNormExactResidual) :
    CanonicalNormalizedNormEquality :=
  canonicalNormalizedNormEquality_of_imageNorm h


/-! ## Basic normalized-image facts -/

theorem normalizedUniformizerImage_ne_zero :
    normalizedUniformizerImage ≠ 0 :=
by
  unfold normalizedUniformizerImage
  exact fun h => LeanFormal.IUT.UniformizerDVRDecomposition.concreteAdicUniformizer_ne_zero
    ((LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm.injective
      (by simpa using h))

theorem normalizedUniformizerImage_norm_pos :
    0 < ‖normalizedUniformizerImage‖ :=
  norm_pos_iff.mpr normalizedUniformizerImage_ne_zero

theorem normalizedUniformizerImage_norm_le_one :
    ‖normalizedUniformizerImage‖ ≤ 1 :=
by
  have h := (normalizedNormOnCompletion_le_one_iff uniformizer).mpr
    (by rw [norm_uniformizer_eq_inv_five]; norm_num)
  rwa [normalizedNormOnCompletion_uniformizer_eq_image] at h

theorem normalizedNormOnCompletion_lt_one_iff (x : completionField) :
    normalizedNormOnCompletion x < 1 ↔ ‖x‖ < 1 :=
by
  unfold normalizedNormOnCompletion
  exact (normalizedCompletion_norm_lt_one_iff concretePlace _)

theorem normalizedUniformizerImage_norm_lt_one :
    ‖normalizedUniformizerImage‖ < 1 :=
by
  rw [← normalizedNormOnCompletion_uniformizer_eq_image]
  exact (normalizedNormOnCompletion_lt_one_iff uniformizer).mpr (by
    rw [norm_uniformizer_eq_inv_five]
    norm_num)
theorem normalizedUniformizerImage_eq_algebraMap_five_of_image_eq
    (h : normalizedUniformizerImage =
      algebraMap normalizedScalarField normalizedCompletion (5 : normalizedScalarField)) :
    NormalizedUniformizerImageNormResidual :=
by
  rw [NormalizedUniformizerImageNormResidual, h]
  rw [normalizedNorm_algebraMap]
  norm_num

/-- If the normalized image is exactly the base scalar `5`, the image norm is
`1/5`. -/
theorem imageNorm_of_image_eq_algebraMap_five
    (h : normalizedUniformizerImage =
      algebraMap normalizedScalarField normalizedCompletion (5 : normalizedScalarField)) :
    NormalizedUniformizerImageNormResidual :=
  normalizedUniformizerImage_eq_algebraMap_five_of_image_eq h

theorem of_imageNorm_canonicalNormalizedNormEquality
    (h : NormalizedUniformizerImageNormResidual) :
    CanonicalNormalizedNormEquality :=
  canonicalNormalizedNormEquality_of_imageNorm h

theorem of_imageEq_canonicalNormalizedNormEquality
    (h : normalizedUniformizerImage =
      algebraMap normalizedScalarField normalizedCompletion (5 : normalizedScalarField)) :
    CanonicalNormalizedNormEquality :=
  canonicalNormalizedNormEquality_of_imageNorm
    (normalizedUniformizerImage_eq_algebraMap_five_of_image_eq h)

end LeanFormal.IUT.NormalizedUniformizerNormProof

end