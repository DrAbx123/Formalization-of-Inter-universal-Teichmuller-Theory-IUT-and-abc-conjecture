import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedGeneratorValuationExponentProof
import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedUniformizerImageGenerator
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceLogShellDiscrepancy
import Mathlib.RingTheory.ClassGroup.Basic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# Principal ideal of the normalized uniformizer image

Goal: `NormalizedGeneratorIdealEquality`, i.e. the principal fractional ideal
of the normalized image is the maximal ideal of the normalized completion
integers.

The normalized completion ring equivalence identifies the normalized integer
ring with the canonical integer ring, and the image of the canonical
uniformizer is a generator of the normalized maximal ideal.  This file states
the exact transport input and reduces the ideal equality to:

1. the canonical principal-ideal equality for the actual uniformizer;
2. the integer-ideal transport along `normalizedCompletionRingEquiv`.

Both are recorded as explicit propositions.  The principal-ideal/exponent
bridge is then combined with the surjectivity representative of exponent one.

No fake ideal equality, no card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.NormalizedGeneratorIdealEqualityProof

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.NormalizedGeneratorValuationExponentProof
open LeanFormal.IUT.NormalizedUniformizerImageGenerator
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

local instance gaussianIdealEqualityIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

local instance factFivePrime : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The normalized completion. -/
abbrev normalizedCompletion : Type :=
  LeanFormal.IUT.NormalizedCompletion concretePlace

/-- The canonical completion. -/
abbrev completionField : Type :=
  LeanFormal.IUT.NormalizedLogNormComparison.completionField

/-- Normalized integers. -/
abbrev normalizedIntegers : Subring normalizedCompletion :=
  LeanFormal.IUT.LocalFieldIntegralUnits.Integers normalizedCompletion

/-- Canonical completion integers. -/
abbrev canonicalIntegers : Subring completionField :=
  LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField

/-- The normalized image unit. -/
noncomputable abbrev normalizedImageUnit : normalizedCompletionˣ :=
  LeanFormal.IUT.NormalizedGeneratorNormValue.normalizedUniformizerImageUnit

/-- The canonical uniformizer as a unit. -/
noncomputable def canonicalUniformizerUnit : completionFieldˣ :=
  Units.mk0 LeanFormal.IUT.ClosedBallCompactness.uniformizer
    (LeanFormal.IUT.UniformizerDVRDecomposition.concreteAdicUniformizer_ne_zero)

/-! ## Fractional ideals -/

/-- The normalized image principal ideal. -/
noncomputable def normalizedImagePrincipalIdeal :
    FractionalIdeal (normalizedIntegers)⁰ normalizedCompletion :=
  toPrincipalIdeal normalizedIntegers normalizedCompletion normalizedImageUnit

/-- The normalized maximal ideal as a fractional ideal. -/
noncomputable def normalizedMaximalIdeal :
    FractionalIdeal (normalizedIntegers)⁰ normalizedCompletion :=
  (Ideal.maximalIdeal normalizedIntegers :
    FractionalIdeal (normalizedIntegers)⁰ normalizedCompletion)

/-- The canonical image principal ideal. -/
noncomputable def canonicalImagePrincipalIdeal :
    FractionalIdeal (canonicalIntegers)⁰ completionField :=
  toPrincipalIdeal canonicalIntegers completionField canonicalUniformizerUnit

/-- The canonical maximal ideal as a fractional ideal. -/
noncomputable def canonicalMaximalIdeal :
    FractionalIdeal (canonicalIntegers)⁰ completionField :=
  (Ideal.maximalIdeal canonicalIntegers :
    FractionalIdeal (canonicalIntegers)⁰ completionField)

/-! ## The two exact transport inputs -/

/-- The actual uniformizer generates the canonical maximal ideal. -/
def CanonicalUniformizerPrincipalIdealEquality : Prop :=
  canonicalImagePrincipalIdeal = canonicalMaximalIdeal

/-- The integer-ideal transport along the normalized ring equivalence: the
normalized principal ideal corresponds to the canonical one.  This is the
ideal-level consequence of `normalizedCompletionRingEquiv_image_integers`. -/
def NormalizedPrincipalIdealTransport : Prop :=
  (normalizedImagePrincipalIdeal = normalizedMaximalIdeal) ↔
    (canonicalImagePrincipalIdeal = canonicalMaximalIdeal)

/-- Normalized ideal equality follows from the canonical uniformizer generator
and the ideal transport. -/
theorem normalizedGeneratorIdealEquality_of_inputs
    (hcanonical : CanonicalUniformizerPrincipalIdealEquality)
    (htransport : NormalizedPrincipalIdealTransport) :
    NormalizedGeneratorIdealEquality :=
by
  unfold NormalizedGeneratorIdealEquality
  exact htransport.mpr hcanonical

/-! ## Principal ideal to exponent -/

/-- A unit whose principal ideal is the maximal ideal has valuation exponent
one.  This is the exact principal-ideal/exponent bridge. -/
theorem exponent_one_of_principalIdeal_maximal
    (h : MaximalIdealPrincipalIdealExponentInput)
    (u : (concretePlace.maximalIdeal.adicCompletion GaussianField)ˣ)
    (hu : (toPrincipalIdeal
      (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField)
      (concretePlace.maximalIdeal.adicCompletion GaussianField) u :
        FractionalIdeal
          (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField)⁰
          (concretePlace.maximalIdeal.adicCompletion GaussianField)) =
      (Ideal.maximalIdeal
        (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField) :
        FractionalIdeal
          (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField)⁰
          (concretePlace.maximalIdeal.adicCompletion GaussianField))) :
    completionValuationExponent concretePlace.maximalIdeal u = 1 :=
  h u hu

theorem valuationExactResidual_of_inputs
    (hcanonical : CanonicalUniformizerPrincipalIdealEquality)
    (htransport : NormalizedPrincipalIdealTransport)
    (hexp : MaximalIdealPrincipalIdealExponentInput) :
    NormalizedGeneratorValuationExactResidual :=
  ⟨normalizedGeneratorIdealEquality_of_inputs hcanonical htransport, hexp⟩

theorem valuationExponentInput_of_inputs
    (hcanonical : CanonicalUniformizerPrincipalIdealEquality)
    (htransport : NormalizedPrincipalIdealTransport)
    (hexp : MaximalIdealPrincipalIdealExponentInput) :
    NormalizedGeneratorValuationExponentInput :=
  valuationExponentInput_of_exactResidual
    (valuationExactResidual_of_inputs hcanonical htransport hexp)

/-! ## Exact residual -/

/-- The exact residual for the ideal equality: canonical uniformizer generator
condition plus the normalized principal-ideal transport. -/
def NormalizedGeneratorIdealEqualityExactResidual : Prop :=
  CanonicalUniformizerPrincipalIdealEquality ∧ NormalizedPrincipalIdealTransport

theorem normalizedGeneratorIdealEquality_of_exactResidual
    (h : NormalizedGeneratorIdealEqualityExactResidual) :
    NormalizedGeneratorIdealEquality :=
  normalizedGeneratorIdealEquality_of_inputs h.1 h.2

theorem valuationExactResidual_of_idealAndBridge
    (h : NormalizedGeneratorIdealEqualityExactResidual)
    (hexp : MaximalIdealPrincipalIdealExponentInput) :
    NormalizedGeneratorValuationExactResidual :=
  valuationExactResidual_of_inputs h.1 h.2 hexp

theorem spectralInput_of_idealAndBridge
    (h : NormalizedGeneratorIdealEqualityExactResidual)
    (hexp : MaximalIdealPrincipalIdealExponentInput)
    (hlog : NormalizedLogNormInput) :
    NormalizedSpectralUniformizerInput :=
  spectralInput_of_exactResidual
    (valuationExactResidual_of_idealAndBridge h hexp) hlog


/-! ## Projections and consumer forms -/

theorem normalizedImagePrincipalIdeal_def :
    normalizedImagePrincipalIdeal =
      toPrincipalIdeal normalizedIntegers normalizedCompletion normalizedImageUnit :=
  rfl

theorem normalizedMaximalIdeal_def :
    normalizedMaximalIdeal =
      (Ideal.maximalIdeal normalizedIntegers :
        FractionalIdeal (normalizedIntegers)⁰ normalizedCompletion) :=
  rfl

theorem canonicalImagePrincipalIdeal_def :
    canonicalImagePrincipalIdeal =
      toPrincipalIdeal canonicalIntegers completionField canonicalUniformizerUnit :=
  rfl

theorem canonicalMaximalIdeal_def :
    canonicalMaximalIdeal =
      (Ideal.maximalIdeal canonicalIntegers :
        FractionalIdeal (canonicalIntegers)⁰ completionField) :=
  rfl

theorem normalizedGeneratorIdealEquality_iff :
    NormalizedGeneratorIdealEquality ↔
      normalizedImagePrincipalIdeal = normalizedMaximalIdeal :=
  Iff.rfl

theorem canonicalUniformizerPrincipalIdealEquality_iff :
    CanonicalUniformizerPrincipalIdealEquality ↔
      canonicalImagePrincipalIdeal = canonicalMaximalIdeal :=
  Iff.rfl

theorem normalizedPrincipalIdealTransport_iff :
    NormalizedPrincipalIdealTransport ↔
      (normalizedImagePrincipalIdeal = normalizedMaximalIdeal ↔
        canonicalImagePrincipalIdeal = canonicalMaximalIdeal) :=
  Iff.rfl

theorem exactResidual_canonical :
    NormalizedGeneratorIdealEqualityExactResidual →
      CanonicalUniformizerPrincipalIdealEquality :=
  fun h => h.1

theorem exactResidual_transport :
    NormalizedGeneratorIdealEqualityExactResidual →
      NormalizedPrincipalIdealTransport :=
  fun h => h.2

theorem normalizedIdealEquality_of_exactResidual_apply
    (h : NormalizedGeneratorIdealEqualityExactResidual) :
    normalizedImagePrincipalIdeal = normalizedMaximalIdeal :=
  normalizedGeneratorIdealEquality_of_exactResidual h

/-- The exact residual, with the principal-ideal/exponent bridge, closes the
valuation-exponent exact residual. -/
theorem valuationExactResidual_of_exactResidual
    (h : NormalizedGeneratorIdealEqualityExactResidual)
    (hexp : MaximalIdealPrincipalIdealExponentInput) :
    NormalizedGeneratorValuationExactResidual :=
  valuationExactResidual_of_idealAndBridge h hexp

end LeanFormal.IUT.NormalizedGeneratorIdealEqualityProof

end
