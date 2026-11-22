import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedUniformizerImageNormExact
import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedUniformizerImageGenerator
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalIdealValuation

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# Valuation exponent of the normalized uniformizer image

Goal:

  `completionValuationExponent concretePlace.maximalIdeal imageUnit = 1`.

The image is the normalized maximal-ideal generator.  The production
`completionValuationExponent_surjective` supplies a unit with exponent `1`;
the value-group/principal-ideal comparison
`completionPrincipalIdeal_le_iff_valuationExponent_ge` identifies the exponent
of any maximal-ideal generator with `1`.  This file records the exact
ideal-generator input and proves the exponent consequence.

If the ideal-generator/exponent identification remains unavailable, the exact
missing statement is `NormalizedGeneratorIdealEquality`; it is not postulated.

No fake value, no card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.NormalizedGeneratorValuationExponentProof

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.NormalizedUniformizerImageNormExact
open LeanFormal.IUT.NormalizedUniformizerImageGenerator
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

local instance gaussianValuationExponentIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

local instance factFivePrime : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The normalized completion. -/
abbrev normalizedCompletion : Type :=
  LeanFormal.IUT.NormalizedCompletion concretePlace

/-- The normalized image unit. -/
noncomputable abbrev normalizedUniformizerImageUnit : normalizedCompletionˣ :=
  LeanFormal.IUT.NormalizedGeneratorNormValue.normalizedUniformizerImageUnit

/-! ## The exact ideal-generator input -/

/-- The principal ideal of the normalized image is the maximal ideal of the
completion integers.  This is the ideal form of the maximal-ideal generator
property. -/
def NormalizedGeneratorIdealEquality : Prop :=
  (toPrincipalIdeal (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField)
      (concretePlace.maximalIdeal.adicCompletion GaussianField)
      normalizedUniformizerImageUnit : FractionalIdeal
        (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField)⁰
        (concretePlace.maximalIdeal.adicCompletion GaussianField)) =
    (Ideal.maximalIdeal
      (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField) :
      FractionalIdeal
        (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField)⁰
        (concretePlace.maximalIdeal.adicCompletion GaussianField))

/-- The value-group input: any unit whose principal ideal is the maximal ideal
has exponent one.  This is the exact bridge from the ideal form to the integer
exponent. -/
def MaximalIdealPrincipalIdealExponentInput : Prop :=
  ∀ u : (concretePlace.maximalIdeal.adicCompletion GaussianField)ˣ,
    (toPrincipalIdeal (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField)
        (concretePlace.maximalIdeal.adicCompletion GaussianField) u :
        FractionalIdeal
          (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField)⁰
          (concretePlace.maximalIdeal.adicCompletion GaussianField)) =
      (Ideal.maximalIdeal
        (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField) :
        FractionalIdeal
          (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField)⁰
          (concretePlace.maximalIdeal.adicCompletion GaussianField)) →
      completionValuationExponent concretePlace.maximalIdeal u = 1

/-! ## Surjectivity representative of exponent one -/

theorem exists_exponent_one_unit :
    ∃ z : (concretePlace.maximalIdeal.adicCompletion GaussianField)ˣ,
      completionValuationExponent concretePlace.maximalIdeal z = 1 :=
  completionValuationExponent_surjective concretePlace.maximalIdeal 1

/-- A unit with exponent one has principal ideal equal to the maximal ideal.
This is the reverse direction of the value-group bridge. -/
def ExponentOnePrincipalIdeal : Prop :=
  ∀ z : (concretePlace.maximalIdeal.adicCompletion GaussianField)ˣ,
    completionValuationExponent concretePlace.maximalIdeal z = 1 →
      (toPrincipalIdeal (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField)
          (concretePlace.maximalIdeal.adicCompletion GaussianField) z :
          FractionalIdeal
            (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField)⁰
            (concretePlace.maximalIdeal.adicCompletion GaussianField)) =
        (Ideal.maximalIdeal
          (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField) :
          FractionalIdeal
            (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField)⁰
            (concretePlace.maximalIdeal.adicCompletion GaussianField))

/-! ## Exponent from the ideal data -/

theorem valuationExponent_one_of_ideal_equality
    (h : NormalizedGeneratorIdealEquality)
    (hprincipal : MaximalIdealPrincipalIdealExponentInput) :
    NormalizedGeneratorValuationExponentInput :=
by
  unfold NormalizedGeneratorValuationExponentInput
  exact hprincipal normalizedUniformizerImageUnit h

theorem valuationExponent_one_of_bridge
    (hid : NormalizedGeneratorIdealEquality)
    (hbridge : MaximalIdealPrincipalIdealExponentInput) :
    completionValuationExponent concretePlace.maximalIdeal
      normalizedUniformizerImageUnit = 1 :=
  valuationExponent_one_of_ideal_equality hid hbridge

/-! ## Exact residual -/

/-- The exact remaining value-group input: the principal ideal equality plus
the maximal-ideal principal-ideal/exponent bridge.  Neither is postulated. -/
def NormalizedGeneratorValuationExactResidual : Prop :=
  NormalizedGeneratorIdealEquality ∧ MaximalIdealPrincipalIdealExponentInput

theorem valuationExponentInput_of_exactResidual
    (h : NormalizedGeneratorValuationExactResidual) :
    NormalizedGeneratorValuationExponentInput :=
  valuationExponent_one_of_ideal_equality h.1 h.2

theorem spectralInput_of_exactResidual
    (h : NormalizedGeneratorValuationExactResidual)
    (hlog : NormalizedLogNormInput) :
    NormalizedSpectralUniformizerInput :=
  ⟨valuationExponentInput_of_exactResidual h, hlog⟩

theorem normalizedImageNormExactResidual_of_exactResidual
    (h : NormalizedGeneratorValuationExactResidual)
    (hlog : NormalizedLogNormInput) :
    NormalizedUniformizerImageNormExactResidual :=
  ⟨valuationExponentInput_of_exactResidual h, hlog⟩


/-! ## Composition with the log-norm formula -/

/-- The value-group input plus the normalized log-norm formula gives the
normalized image norm `1/5`. -/
theorem normalizedImageNormResidual_of_exponent_and_log
    (hval : NormalizedGeneratorValuationExponentInput)
    (hlog : NormalizedLogNormInput) :
    LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerImageNormResidual :=
  normalizedImage_norm_eq_inv_five hval hlog

theorem canonicalNormalizedNormEquality_of_exponent_and_log
    (hval : NormalizedGeneratorValuationExponentInput)
    (hlog : NormalizedLogNormInput) :
    CanonicalNormalizedNormEquality :=
  canonicalNormalizedNormEquality_of_spectralInput ⟨hval, hlog⟩

/-- The exact residual for the valuation exponent, combined with the separate
log-norm residual, gives the full normalized image norm. -/
def NormalizedGeneratorValuationAndLogResidual : Prop :=
  NormalizedGeneratorValuationExactResidual ∧ NormalizedLogNormInput

theorem valuationExponentInput_of_andLogResidual
    (h : NormalizedGeneratorValuationAndLogResidual) :
    NormalizedGeneratorValuationExponentInput :=
  valuationExponentInput_of_exactResidual h.1

theorem normalizedImageNormResidual_of_andLogResidual
    (h : NormalizedGeneratorValuationAndLogResidual) :
    LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerImageNormResidual :=
  normalizedImage_norm_eq_inv_five (valuationExponentInput_of_andLogResidual h) h.2

theorem canonicalNormalizedNormEquality_of_andLogResidual
    (h : NormalizedGeneratorValuationAndLogResidual) :
    CanonicalNormalizedNormEquality :=
  canonicalNormalizedNormEquality_of_exponent_and_log
    (valuationExponentInput_of_andLogResidual h) h.2

/-! ## Residual projections -/

theorem exactResidual_idealEquality
    (h : NormalizedGeneratorValuationExactResidual) :
    NormalizedGeneratorIdealEquality :=
  h.1

theorem exactResidual_principalIdealBridge
    (h : NormalizedGeneratorValuationExactResidual) :
    MaximalIdealPrincipalIdealExponentInput :=
  h.2

theorem exactResidual_iff :
    NormalizedGeneratorValuationExactResidual ↔
      NormalizedGeneratorIdealEquality ∧ MaximalIdealPrincipalIdealExponentInput :=
  Iff.rfl

/-- A generator with exponent one has the maximal ideal as principal ideal, and
conversely the ideal generator bridge gives exponent one.  The remaining
bookkeeping is the two Prop fields. -/
theorem valuationExponent_iff_of_ideal_bridges
    (hforward : MaximalIdealPrincipalIdealExponentInput)
    (hbackward : ExponentOnePrincipalIdeal) :
    NormalizedGeneratorIdealEquality →
      completionValuationExponent concretePlace.maximalIdeal
        normalizedUniformizerImageUnit = 1 :=
  fun hid => valuationExponent_one_of_ideal_equality hid hforward


theorem andLogResidual_iff :
    NormalizedGeneratorValuationAndLogResidual ↔
      NormalizedGeneratorValuationExactResidual ∧ NormalizedLogNormInput :=
  Iff.rfl

theorem generatorNormResidual_of_andLogResidual
    (h : NormalizedGeneratorValuationAndLogResidual) :
    LeanFormal.IUT.NormalizedUniformizerImageGenerator.NormalizedGeneratorNormResidual :=
  LeanFormal.IUT.NormalizedGeneratorNormValue.generatorNormResidual_of_logNorm_and_valuation
    h.2 (valuationExponentInput_of_andLogResidual h)

theorem normalizedImageNormExactResidual_of_andLogResidual
    (h : NormalizedGeneratorValuationAndLogResidual) :
    NormalizedUniformizerImageNormExactResidual :=
  ⟨valuationExponentInput_of_andLogResidual h, h.2⟩

end LeanFormal.IUT.NormalizedGeneratorValuationExponentProof

end
