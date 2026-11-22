import LeanFormal.IUT.Foundations.AlgebraicGeometry.GeneralNormalizedNormFinal

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# Stable consumer for the general normalized norm formulas

Consumes `GeneralNormalizedNormFinal` and exposes:

* the base-scalar valuation identity;
* the normalized spectral bridge;
* the general normalized norm formula;
* the general logarithmic formula;
* `NormalizedCanonicalPowerComparison` on the normalized carrier and its
  canonical-carrier form.

No new hypothesis and no new residual: every declaration is a re-export.
No fake norm formula.

No card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.GeneralNormalizedNormConsumer

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.GeneralNormalizedNormFinal

universe u

variable {F : Type u} [Field F] [NumberField F]
  (place : NumberField.FinitePlace F)

abbrev K : Type u := PadicScalarField place
abbrev N : Type u := NormalizedCompletion place
abbrev C : Type u := place.maximalIdeal.adicCompletion F

/-! ## Base-scalar identity -/

theorem baseScalarValuationIdentity_consumer
    (q : PadicScalarField place) (hq : q ≠ 0) :
    ∃ m : ℤ,
      (Valued.v (algebraMap (PadicScalarField place) (C place) q) :
        WithZero (Multiplicative ℤ)) =
        WithZero.exp (-(m * (BaseScalarValuationRelation.ramification place : ℤ))) :=
  (baseScalarValuationIdentity place q hq).imp (fun m hm => hm.2)

theorem baseScalarValuationIdentity_exists
    (q : PadicScalarField place) (hq : q ≠ 0) :
    ∃ m : ℤ, (Valued.v (algebraMap (PadicScalarField place) (C place) q) :
      WithZero (Multiplicative ℤ)) =
      WithZero.exp (-(m * (BaseScalarValuationRelation.ramification place : ℤ))) :=
  baseScalarValuationIdentity_consumer place q hq

/-! ## Spectral bridge -/

theorem normalizedNorm_eq_spectralNorm_consumer (x : N place) :
    ‖x‖ = spectralNorm (K place) (N place) x :=
  normalizedNorm_eq_spectralNorm_final place x

theorem normalizedNorm_eq_spectralNorm_apply (x : N place) :
    ‖x‖ = spectralNorm (K place) (N place) x :=
  normalizedNorm_eq_spectralNorm_consumer place x

/-! ## General formulas -/

theorem generalNormalizedNormFormula_consumer (x : N place) :
    ‖x‖ = (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^
      (-((nu place x : ℝ) /
        ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ))) :=
  generalNormalizedNormFormula place x

theorem generalNormalizedNormFormula_apply (x : N place) :
    ‖x‖ = (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^
      (-((nu place x : ℝ) /
        ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ))) :=
  generalNormalizedNormFormula_consumer place x

theorem generalNormalizedLogFormula_consumer (x : N place) :
    Real.log ‖x‖ = -(((nu place x : ℝ) *
      Real.log (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ)) /
      ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ)) :=
  generalNormalizedLogFormula place x

theorem generalNormalizedLogFormula_apply (x : N place) :
    Real.log ‖x‖ = -(((nu place x : ℝ) *
      Real.log (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ)) /
      ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ)) :=
  generalNormalizedLogFormula_consumer place x

/-! ## Power comparison -/

theorem normalizedCanonicalPowerComparison_consumer
    (x : N place) (hx : x ≠ 0) :
    ‖x‖ ^ (relativeCompletionDegree (k := ℚ) place : ℕ) =
      ((Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^ nu place x)⁻¹ :=
  normalizedCanonicalPowerComparison_final place x hx

theorem normalizedCanonicalPowerComparison_carrier_consumer
    (x : C place) (hx : x ≠ 0) :
    (spectralNorm (K place) (C place) x) ^
        (relativeCompletionDegree (k := ℚ) place : ℕ) =
      ((Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^ nu place x)⁻¹ :=
  normalizedCanonicalPowerComparison_carrier place x hx

/-! ## Packaged consumer -/

structure GeneralNormalizedNormConsumerData where
  baseScalar : ∀ (q : PadicScalarField place), q ≠ 0 →
    ∃ m : ℤ, (Valued.v (algebraMap (PadicScalarField place) (C place) q) :
      WithZero (Multiplicative ℤ)) =
      WithZero.exp (-(m * (BaseScalarValuationRelation.ramification place : ℤ)))
  normFormula : ∀ x : N place,
    ‖x‖ = (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^
      (-((nu place x : ℝ) /
        ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ)))
  logFormula : ∀ x : N place,
    Real.log ‖x‖ = -(((nu place x : ℝ) *
      Real.log (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ)) /
      ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ))
  powerComparison : ∀ x : N place, x ≠ 0 →
    ‖x‖ ^ (relativeCompletionDegree (k := ℚ) place : ℕ) =
      ((Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^ nu place x)⁻¹

noncomputable def generalNormalizedNormConsumerData :
    GeneralNormalizedNormConsumerData place :=
  { baseScalar := baseScalarValuationIdentity_consumer place
    normFormula := generalNormalizedNormFormula_consumer place
    logFormula := generalNormalizedLogFormula_consumer place
    powerComparison := normalizedCanonicalPowerComparison_consumer place }

theorem consumer_normFormula :
    ∀ x : N place, ‖x‖ = (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^
      (-((nu place x : ℝ) /
        ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ))) :=
  generalNormalizedNormConsumerData.normFormula

theorem consumer_powerComparison :
    ∀ x : N place, x ≠ 0 →
      ‖x‖ ^ (relativeCompletionDegree (k := ℚ) place : ℕ) =
        ((Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^ nu place x)⁻¹ :=
  generalNormalizedNormConsumerData.powerComparison

end LeanFormal.IUT.GeneralNormalizedNormConsumer

end
