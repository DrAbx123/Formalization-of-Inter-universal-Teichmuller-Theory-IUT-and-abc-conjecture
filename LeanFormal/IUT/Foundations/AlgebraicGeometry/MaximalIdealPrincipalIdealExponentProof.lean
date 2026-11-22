import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedPrincipalIdealTransportProof
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalIdealValuation
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.ClassGroup.Basic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# Principal-ideal/exponent bridge

Goal:

  `MaximalIdealPrincipalIdealExponentInput`: a completion unit whose principal
  ideal is the maximal ideal has classical valuation exponent `1`.

Strategy:
* production `completionValuationExponent_surjective` gives a unit `z` of
  exponent `1`;
* the production ideal-inclusion/exponent comparison shows `(z)` is the
  maximal ideal (compare with the actual uniformizer unit);
* if `(u)` is also maximal, then `toPrincipalIdeal u = toPrincipalIdeal z`, so
  `spanSingleton u = spanSingleton z`;
* `spanSingleton_eq_spanSingleton` gives an integral unit `w` with `w • u = z`;
* integral units have exponent `0`, hence `exponent u = exponent z = 1`.

No fake value, no card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.MaximalIdealPrincipalIdealExponentProof

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.NormalizedPrincipalIdealTransportProof
open LeanFormal.IUT.NormalizedGeneratorIdealEqualityProof
open LeanFormal.IUT.CanonicalUniformizerPrincipalIdealEqualityProof
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

local instance gaussianExponentBridgeIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

local instance factFivePrime : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The canonical completion. -/
abbrev completionField : Type :=
  LeanFormal.IUT.NormalizedGeneratorIdealEqualityProof.completionField

/-- The canonical completion integers. -/
abbrev canonicalIntegers : Subring completionField :=
  LeanFormal.IUT.NormalizedGeneratorIdealEqualityProof.canonicalIntegers

/-- The canonical uniformizer unit. -/
noncomputable abbrev canonicalUniformizerUnit : completionFieldˣ :=
  LeanFormal.IUT.CanonicalUniformizerPrincipalIdealEqualityProof.canonicalUniformizerUnit

/-! ## Exponent of the actual uniformizer -/

theorem canonicalUniformizer_exponent :
    completionValuationExponent concretePlace.maximalIdeal
      canonicalUniformizerUnit = 1 :=
by
  rw [completionValuationExponent_eq_neg_log]
  rw [CanonicalUniformizerPrincipalIdealEqualityProof.canonicalUniformizerUnit_coe]
  rw [CanonicalUniformizerPrincipalIdealEqualityProof.canonicalUniformizerIntegral_valued]
  rw [WithZero.log_exp]
  norm_num

/-! ## Exponent-one unit from surjectivity -/

noncomputable def exponentOneUnit : completionFieldˣ :=
  Classical.choose (completionValuationExponent_surjective concretePlace.maximalIdeal 1)

theorem exponentOneUnit_spec :
    completionValuationExponent concretePlace.maximalIdeal exponentOneUnit = 1 :=
  Classical.choose_spec (completionValuationExponent_surjective concretePlace.maximalIdeal 1)

/-! ## Principal ideal of an exponent-one unit -/

theorem principalIdeal_equal_of_exponent_equal
    {x y : completionFieldˣ}
    (h : completionValuationExponent concretePlace.maximalIdeal x =
      completionValuationExponent concretePlace.maximalIdeal y) :
    (toPrincipalIdeal canonicalIntegers completionField x :
        FractionalIdeal (canonicalIntegers)⁰ completionField) =
      (toPrincipalIdeal canonicalIntegers completionField y :
        FractionalIdeal (canonicalIntegers)⁰ completionField) :=
by
  -- both ideal inclusions follow from the exponent comparison
  apply le_antisymm
  · rw [completionPrincipalIdeal_le_iff_valuationExponent_ge]
    rw [h]
  · rw [completionPrincipalIdeal_le_iff_valuationExponent_ge]
    rw [h]

theorem exponentOneUnit_principalIdeal_maximal :
    (toPrincipalIdeal canonicalIntegers completionField exponentOneUnit :
        FractionalIdeal (canonicalIntegers)⁰ completionField) =
      canonicalMaximalIdeal :=
by
  rw [← canonicalImagePrincipalIdeal_eq_canonicalMaximalIdeal]
  rw [canonicalImagePrincipalIdeal, coe_toPrincipalIdeal]
  -- compare with the actual uniformizer using equal exponents
  have h := principalIdeal_equal_of_exponent_equal
    (x := exponentOneUnit) (y := canonicalUniformizerUnit) (by
      rw [exponentOneUnit_spec, canonicalUniformizer_exponent])
  simpa only [coe_toPrincipalIdeal] using h

/-! ## The bridge -/

theorem maximalIdealPrincipalIdealExponentInput_holds :
    MaximalIdealPrincipalIdealExponentInput :=
by
  intro u hu
  -- compare `(u)` with `(exponentOneUnit)`
  have hIdeal : (toPrincipalIdeal canonicalIntegers completionField u :
      FractionalIdeal (canonicalIntegers)⁰ completionField) =
      (toPrincipalIdeal canonicalIntegers completionField exponentOneUnit :
        FractionalIdeal (canonicalIntegers)⁰ completionField) :=
    hu.trans exponentOneUnit_principalIdeal_maximal.symm
  -- `toPrincipalIdeal` equality gives `spanSingleton` equality
  have hspan : spanSingleton (canonicalIntegers)⁰ (u : completionField) =
      spanSingleton (canonicalIntegers)⁰ (exponentOneUnit : completionField) :=
  by
    simpa [coe_toPrincipalIdeal] using hIdeal
  obtain ⟨w, hw⟩ := (spanSingleton_eq_spanSingleton.mp hspan)
  -- `w` is an integral unit, hence exponent zero
  have hwmem : w ∈ (canonicalIntegers)ˣ := by
    -- w is the unit supplied by the fractional ideal equality
    exact w.property
  have hwzero : completionValuationExponent concretePlace.maximalIdeal
      (Units.map (algebraMap canonicalIntegers completionField).toMonoidHom w) = 0 :=
  by
    rw [completionValuationExponent_eq_zero_iff_mem_integralUnits]
    exact (Units.map (algebraMap canonicalIntegers completionField).toMonoidHom w).property
  -- `w • u = exponentOneUnit`, so exponents add
  have hmul : exponentOneUnit =
      Units.map (algebraMap canonicalIntegers completionField).toMonoidHom w * u :=
  by
    ext
    simpa using hw
  have hspec : completionValuationExponent concretePlace.maximalIdeal
      (Units.map (algebraMap canonicalIntegers completionField).toMonoidHom w * u) = 1 := by
    rw [← hmul]
    exact exponentOneUnit_spec
  rw [completionValuationExponent_mul, hwzero] at hspec
  linarith


/-! ## Auxiliary principal-ideal facts -/

theorem toPrincipalIdeal_coe_eq_spanSingleton (x : completionFieldˣ) :
    (toPrincipalIdeal canonicalIntegers completionField x :
        FractionalIdeal (canonicalIntegers)⁰ completionField) =
      spanSingleton (canonicalIntegers)⁰ (x : completionField) :=
  coe_toPrincipalIdeal x

theorem exponentZero_of_integralUnit
    (w : (canonicalIntegers)ˣ) :
    completionValuationExponent concretePlace.maximalIdeal
      (Units.map (algebraMap canonicalIntegers completionField).toMonoidHom w) = 0 :=
by
  rw [completionValuationExponent_eq_zero_iff_mem_integralUnits]
  exact (Units.map (algebraMap canonicalIntegers completionField).toMonoidHom w).property

/-! ## Surjectivity representative reconstruction -/

theorem exponentOneUnit_principalIdeal_eq_canonicalUniformizerIdeal :
    (toPrincipalIdeal canonicalIntegers completionField exponentOneUnit :
        FractionalIdeal (canonicalIntegers)⁰ completionField) =
      canonicalImagePrincipalIdeal :=
  by
  rw [canonicalImagePrincipalIdeal, coe_toPrincipalIdeal]
  symm
  exact exponentOneUnit_principalIdeal_maximal.trans
    canonicalMaximalIdeal_eq_principalIdeal

/-! ## Consumer chain -/

theorem normalizedGeneratorValuationExactResidual_holds :
    NormalizedGeneratorValuationExactResidual :=
  normalizedGeneratorValuationExactResidual_of_bridge
    maximalIdealPrincipalIdealExponentInput_holds

theorem normalizedGeneratorValuationExponentInput_holds :
    NormalizedGeneratorValuationExponentInput :=
  normalizedGeneratorValuationExponentInput_of_bridge
    maximalIdealPrincipalIdealExponentInput_holds

theorem normalizedGeneratorNormResidual_of_logNorm
    (hlog : NormalizedLogNormInput) :
    LeanFormal.IUT.NormalizedUniformizerImageGenerator.NormalizedGeneratorNormResidual :=
  LeanFormal.IUT.NormalizedGeneratorNormValue.generatorNormResidual_of_logNorm_and_valuation
    hlog normalizedGeneratorValuationExponentInput_holds

theorem canonicalNormalizedNormEquality_of_logNorm
    (hlog : NormalizedLogNormInput) :
    CanonicalNormalizedNormEquality :=
  LeanFormal.IUT.NormalizedGeneratorNormValue.canonicalNormalizedNormEquality_of_logNorm_and_valuation
    hlog normalizedGeneratorValuationExponentInput_holds


/-! ## Residual/consumer summary -/

theorem maximalIdealPrincipalIdealExponentInput_iff :
    MaximalIdealPrincipalIdealExponentInput ↔
      ∀ u : (concretePlace.maximalIdeal.adicCompletion GaussianField)ˣ,
        (toPrincipalIdeal
          (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField)
          (concretePlace.maximalIdeal.adicCompletion GaussianField) u :
            FractionalIdeal
              (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField)⁰
              (concretePlace.maximalIdeal.adicCompletion GaussianField)) =
          (Ideal.maximalIdeal
            (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField) :
            FractionalIdeal
              (concretePlace.maximalIdeal.adicCompletionIntegers GaussianField)⁰
              (concretePlace.maximalIdeal.adicCompletion GaussianField)) →
          completionValuationExponent concretePlace.maximalIdeal u = 1 :=
  Iff.rfl

theorem exponentOneUnit_principalIdeal_maximal_iff :
    (toPrincipalIdeal canonicalIntegers completionField exponentOneUnit :
        FractionalIdeal (canonicalIntegers)⁰ completionField) =
      canonicalMaximalIdeal :=
  exponentOneUnit_principalIdeal_maximal

theorem maximalIdealPrincipalIdealExponentInput_holds_unconditional :
    MaximalIdealPrincipalIdealExponentInput :=
  maximalIdealPrincipalIdealExponentInput_holds

end LeanFormal.IUT.MaximalIdealPrincipalIdealExponentProof

end