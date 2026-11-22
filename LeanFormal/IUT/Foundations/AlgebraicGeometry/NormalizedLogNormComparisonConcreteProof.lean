import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionNormFormulaActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.CanonicalNormalizedNormEqualityProof
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalIdealValuation

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# Concrete normalized log-norm comparison

Goal: the production missing lemma

  `Example36.NormalizedLogNormComparison concretePlace`.

Its definition is, for every unit `x` of `NormalizedCompletion concretePlace`,

  `Real.log ‖x‖ = -((completionValuationExponent place x * log absNorm place) / d)`,

with `d = relativeCompletionDegree (k := ℚ) place`.

At the concrete place `d = 1` and `absNorm = 5`.  The canonical formula
`norm_eq_absNorm_zpow` gives the same logarithmic form for the transported
element under `normalizedCompletionRingEquiv`.  The proof therefore reduces to
two exact inputs:

1. `CanonicalNormalizedNormEquality`: the pointwise equality of the canonical
   norm and the normalized norm;
2. `NormalizedValueExponentComparison`: the normalized valuation exponent is the
   negative of the canonical valuation exponent of the transported element
   (the sign convention of `completionValuationExponent`).

Both are recorded, not postulated.  No fake norm formula is asserted.

No card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.NormalizedLogNormComparisonConcreteProof

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.CanonicalNormalizedNormEqualityProof
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

local instance gaussianNormalizedLogConcreteIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

local instance factFivePrime : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The normalized completion. -/
abbrev normalizedCompletion : Type :=
  LeanFormal.IUT.NormalizedCompletion concretePlace

/-- The canonical completion. -/
abbrev completionField : Type :=
  LeanFormal.IUT.CanonicalNormalizedNormEqualityProof.completionField

/-- Transport a normalized unit to the canonical field. -/
noncomputable def transportUnit (x : normalizedCompletionˣ) : completionFieldˣ :=
  Units.map (LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).toMonoidHom x

/-! ## The two exact inputs -/

/-- The normalized valuation exponent is the negative of the canonical
valuation exponent of the transported unit. -/
def NormalizedValueExponentComparison : Prop :=
  ∀ x : normalizedCompletionˣ,
    completionValuationExponent concretePlace.maximalIdeal x =
      -WithZero.log (Valued.v ((transportUnit x : completionFieldˣ) : completionField))

/-- The canonical/normalized pointwise norm equality on the transported unit. -/
def CanonicalNormalizedUnitNormEquality : Prop :=
  ∀ x : normalizedCompletionˣ,
    ‖(x : normalizedCompletion)‖ =
      ‖((transportUnit x : completionFieldˣ) : completionField)‖

theorem canonicalNormalizedUnitNormEquality_of_normEquality
    (h : CanonicalNormalizedNormEquality) :
    CanonicalNormalizedUnitNormEquality :=
by
  intro x
  have hx := h ((transportUnit x : completionFieldˣ) : completionField)
  -- unfold the normalized norm on the canonical side
  simpa [CanonicalNormalizedNormEquality, normalizedNormOnCompletion,
    normalizedCompletionRingEquiv, transportUnit] using hx

/-! ## The arithmetic proof -/

theorem normalizedLogNormComparison_of_unit_norm_and_exponent
    (hnorm : CanonicalNormalizedUnitNormEquality)
    (hexp : NormalizedValueExponentComparison) :
    NormalizedLogNormComparison concretePlace :=
by
  intro x
  let y : completionFieldˣ := transportUnit x
  have hy : (y : completionField) ≠ 0 := Units.ne_zero y
  have hcanonical := NumberFieldFinitePlace.norm_eq_absNorm_zpow concretePlace
    (y : completionField) hy
  have hlog := congrArg Real.log hcanonical
  rw [Real.log_zpow] at hlog
  -- replace the canonical norm by the normalized norm
  have hnorm_x := hnorm x
  rw [← hnorm_x] at hlog
  -- replace the canonical valuation exponent by the normalized exponent
  have hexp_x := hexp x
  rw [hexp_x] at hlog
  -- concrete degree and absNorm
  rw [concretePlace_upper_absNorm,
    concreteGaussianFivePlace_relativeCompletionDegree_eq_one] at hlog
  simpa [NormalizedLogNormComparison, y, transportUnit, div_one] using hlog

/-! ## Exact residual -/

/-- The exact pair of missing inputs for the concrete normalized log-norm
formula. -/
def NormalizedLogNormComparisonExactResidual : Prop :=
  CanonicalNormalizedUnitNormEquality ∧ NormalizedValueExponentComparison

theorem normalizedLogNormComparison_of_exactResidual
    (h : NormalizedLogNormComparisonExactResidual) :
    NormalizedLogNormComparison concretePlace :=
  normalizedLogNormComparison_of_unit_norm_and_exponent h.1 h.2

/-! ## Consequences for the generator norm -/

theorem normalizedGeneratorNorm_of_logNormComparison
    (h : NormalizedLogNormComparison concretePlace) :
    LeanFormal.IUT.NormalizedGeneratorNormValue.NormalizedLogNormResidual :=
  h

theorem normalizedGeneratorNorm_of_logNormComparison_and_valuation
    (hlog : NormalizedLogNormComparison concretePlace)
    (hval : LeanFormal.IUT.NormalizedGeneratorNormValue.NormalizedGeneratorValuationResidual) :
    LeanFormal.IUT.NormalizedUniformizerImageGenerator.NormalizedGeneratorNormResidual :=
  LeanFormal.IUT.NormalizedGeneratorNormValue.generatorNormResidual_of_logNorm_and_valuation
    hlog hval

theorem canonicalNormalizedNormEquality_of_logNormComparison_and_valuation
    (hlog : NormalizedLogNormComparison concretePlace)
    (hval : LeanFormal.IUT.NormalizedGeneratorNormValue.NormalizedGeneratorValuationResidual) :
    CanonicalNormalizedNormEquality :=
  LeanFormal.IUT.NormalizedGeneratorNormValue.canonicalNormalizedNormEquality_of_logNorm_and_valuation
    hlog hval


/-! ## Auxiliary transports -/

theorem transportUnit_coe (x : normalizedCompletionˣ) :
    ((transportUnit x : completionFieldˣ) : completionField) =
      (LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace)
        (x : normalizedCompletion) :=
  rfl

theorem transportUnit_ne_zero (x : normalizedCompletionˣ) :
    ((transportUnit x : completionFieldˣ) : completionField) ≠ 0 :=
  Units.ne_zero (transportUnit x)

theorem canonicalLogNorm_transport (x : normalizedCompletionˣ) :
    Real.log ‖((transportUnit x : completionFieldˣ) : completionField)‖ =
      (Multiplicative.toAdd (WithZero.unzero
        (NumberFieldFinitePlace.valuation_ne_zero_of_ne_zero concretePlace
          ((transportUnit x : completionFieldˣ) : completionField)
          (transportUnit_ne_zero x)))) *
        Real.log (Ideal.absNorm concretePlace.maximalIdeal.asIdeal : ℝ) :=
by
  have h := NumberFieldFinitePlace.norm_eq_absNorm_zpow concretePlace
    ((transportUnit x : completionFieldˣ) : completionField) (transportUnit_ne_zero x)
  exact congrArg Real.log h |>.trans (Real.log_zpow _ _)

theorem canonicalLogNorm_transport_eq (x : normalizedCompletionˣ) :
    Real.log ‖((transportUnit x : completionFieldˣ) : completionField)‖ =
      (Multiplicative.toAdd (WithZero.unzero
        (NumberFieldFinitePlace.valuation_ne_zero_of_ne_zero concretePlace
          ((transportUnit x : completionFieldˣ) : completionField)
          (transportUnit_ne_zero x)))) * Real.log 5 :=
by
  rw [canonicalLogNorm_transport, concretePlace_upper_absNorm]

theorem normalizedLogNormComparison_apply
    (h : NormalizedLogNormComparison concretePlace) (x : normalizedCompletionˣ) :
    Real.log ‖(x : normalizedCompletion)‖ =
      -(((completionValuationExponent concretePlace.maximalIdeal x : ℝ) *
          Real.log (Ideal.absNorm concretePlace.maximalIdeal.asIdeal : ℝ)) /
        (relativeCompletionDegree (k := ℚ) concretePlace : ℝ)) :=
  h x

theorem normalizedLogNormComparison_apply_simplified
    (h : NormalizedLogNormComparison concretePlace) (x : normalizedCompletionˣ) :
    Real.log ‖(x : normalizedCompletion)‖ =
      -((completionValuationExponent concretePlace.maximalIdeal x : ℝ) * Real.log 5) :=
by
  rw [normalizedLogNormComparison_apply h x, concretePlace_upper_absNorm,
    concreteGaussianFivePlace_relativeCompletionDegree_eq_one]
  norm_num
  ring

/-! ## Residual projections -/

theorem normalizedLogNormComparisonExactResidual_unit_norm
    (h : NormalizedLogNormComparisonExactResidual) :
    CanonicalNormalizedUnitNormEquality :=
  h.1

theorem normalizedLogNormComparisonExactResidual_exponent
    (h : NormalizedLogNormComparisonExactResidual) :
    NormalizedValueExponentComparison :=
  h.2


/-- The exact residual, when supplied, closes the production missing formula. -/
theorem normalizedLogNormComparison_of_exactResidual_unconditional
    (h : NormalizedLogNormComparisonExactResidual) :
    NormalizedLogNormComparison concretePlace :=
  normalizedLogNormComparison_of_exactResidual h

theorem normalizedLogNormComparisonExactResidual_iff :
    NormalizedLogNormComparisonExactResidual ↔
      CanonicalNormalizedUnitNormEquality ∧ NormalizedValueExponentComparison :=
  Iff.rfl

/-! ## Final consumer chain -/

theorem generatorNormResidual_of_exactResidual
    (h : NormalizedLogNormComparisonExactResidual)
    (hval : LeanFormal.IUT.NormalizedGeneratorNormValue.NormalizedGeneratorValuationResidual) :
    LeanFormal.IUT.NormalizedUniformizerImageGenerator.NormalizedGeneratorNormResidual :=
  LeanFormal.IUT.NormalizedGeneratorNormValue.generatorNormResidual_of_logNorm_and_valuation
    (normalizedLogNormComparison_of_exactResidual h) hval

theorem canonicalNormalizedNormEquality_of_exactResidual
    (h : NormalizedLogNormComparisonExactResidual)
    (hval : LeanFormal.IUT.NormalizedGeneratorNormValue.NormalizedGeneratorValuationResidual) :
    CanonicalNormalizedNormEquality :=
  LeanFormal.IUT.NormalizedGeneratorNormValue.canonicalNormalizedNormEquality_of_logNorm_and_valuation
    (normalizedLogNormComparison_of_exactResidual h) hval

end LeanFormal.IUT.NormalizedLogNormComparisonConcreteProof

end
