import LeanFormal.IUT.Foundations.AlgebraicGeometry.GeneralNormalizedNormConsumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GeneralNormalizedNormFormula

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# Fixed final wiring of the general normalized norm consumer

Fixes the two known defects of the previous wiring file:

* the `maximalIdeal` typo is gone;
* the legacy comparison uses the exact names
  `GeneralNormalizedNormFormula.canonicalNormFromValuation` and the actual
  normalized norm `‖x‖`, not provisional `normalizedNorm` names.

The spectral bridge `normalizedNorm = spectralNorm` is kept as an explicit
isolated Prop and is supplied by the consumer.  No fake norm.
-/

noncomputable section

namespace LeanFormal.IUT.GeneralNormalizedNormFinalWiringFixed

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.GeneralNormalizedNormConsumer
open LeanFormal.IUT.GeneralNormalizedNormFinal
open LeanFormal.IUT.GeneralNormalizedNormBySpectralUniqueness
open LeanFormal.IUT.GeneralNormalizedNormFormula

universe u

variable {F : Type u} [Field F] [NumberField F]
  (place : NumberField.FinitePlace F)

abbrev K : Type u := PadicScalarField place
abbrev N : Type u := NormalizedCompletion place
abbrev C : Type u := place.maximalIdeal.adicCompletion F

theorem canonicalNormFromValuation_eq_absNorm_pow
    (x : N place) (hx : x ≠ 0) :
    GeneralNormalizedNormFormula.canonicalNormFromValuation place x hx =
      (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^ nu place x :=
  rfl

/-! ## Consumer facts with exact names -/

theorem fixed_baseScalar (q : PadicScalarField place) (hq : q ≠ 0) :
    ∃ m : ℤ, (Valued.v (algebraMap (PadicScalarField place) (C place) q) :
      WithZero (Multiplicative ℤ)) =
      WithZero.exp (-(m * (BaseScalarValuationRelation.ramification place : ℤ))) :=
  baseScalarValuationIdentity_consumer place q hq

theorem fixed_normalizedNorm_formula (x : N place) :
    ‖x‖ = (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^
      (-((nu place x : ℝ) /
        ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ))) :=
  generalNormalizedNormFormula_consumer place x

theorem fixed_normalizedLog_formula (x : N place) :
    Real.log ‖x‖ = -(((nu place x : ℝ) *
      Real.log (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ)) /
      ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ)) :=
  generalNormalizedLogFormula_consumer place x

theorem fixed_powerComparison (x : N place) (hx : x ≠ 0) :
    ‖x‖ ^ (relativeCompletionDegree (k := ℚ) place : ℕ) =
      ((Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^ nu place x)⁻¹ :=
  normalizedCanonicalPowerComparison_consumer place x hx

/-! ## Legacy general comparison, exact names -/

theorem fixed_legacyPowerComparison :
    GeneralNormalizedNormFormula.NormalizedCanonicalPowerComparison place :=
by
  intro x hx
  change ‖x‖ ^ (GeneralNormalizedNormFormula.localDegree place : ℕ) =
    (GeneralNormalizedNormFormula.canonicalNormFromValuation place x hx)⁻¹
  rw [canonicalNormFromValuation_eq_absNorm_pow place x hx]
  -- the carrier dereference is the actual normalized norm
  simpa [GeneralNormalizedNormFormula.localDegree] using
    fixed_powerComparison place x hx

theorem fixed_consumerPowerComparison_of_legacy
    (h : GeneralNormalizedNormFormula.NormalizedCanonicalPowerComparison place) :
    ∀ x : N place, x ≠ 0 →
      ‖x‖ ^ (relativeCompletionDegree (k := ℚ) place : ℕ) =
        ((Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^ nu place x)⁻¹ :=
  fun x hx => h x hx

theorem fixed_legacy_iff_consumer :
    GeneralNormalizedNormFormula.NormalizedCanonicalPowerComparison place ↔
      (∀ x : N place, x ≠ 0 →
        ‖x‖ ^ (relativeCompletionDegree (k := ℚ) place : ℕ) =
          ((Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^ nu place x)⁻¹) :=
  ⟨fixed_consumerPowerComparison_of_legacy place,
    fun _ => fixed_legacyPowerComparison place⟩

/-! ## Explicit spectral bridge -/

def NormalizedNormSpectralBridgeProp : Prop :=
  ∀ x : N place, ‖x‖ = spectralNorm (K place) (N place) x

theorem fixed_spectralBridge : NormalizedNormSpectralBridgeProp place :=
  normalizedNorm_eq_spectralNorm_consumer place

/-! ## Packaged fixed wiring -/

structure FixedWiringData where
  baseScalar : ∀ (q : PadicScalarField place), q ≠ 0 →
    ∃ m : ℤ, (Valued.v (algebraMap (PadicScalarField place) (C place) q) :
      WithZero (Multiplicative ℤ)) =
      WithZero.exp (-(m * (BaseScalarValuationRelation.ramification place : ℤ)))
  spectralBridge : NormalizedNormSpectralBridgeProp place
  normalizedFormula : ∀ x : N place,
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

end LeanFormal.IUT.GeneralNormalizedNormFinalWiringFixed

end
noncomputable def fixedWiringData : FixedWiringData place :=
  { baseScalar := fixed_baseScalar place
    spectralBridge := fixed_spectralBridge place
    normalizedFormula := fixed_normalizedNorm_formula place
    logFormula := fixed_normalizedLog_formula place
    powerComparison := fixed_powerComparison place }

theorem fixedWiring_all :
    (∀ x : N place, ‖x‖ = (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^
      (-((nu place x : ℝ) /
        ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ)))) ∧
      (∀ x : N place, x ≠ 0 →
        ‖x‖ ^ (relativeCompletionDegree (k := ℚ) place : ℕ) =
          ((Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^ nu place x)⁻¹) :=
  ⟨fixed_normalizedNorm_formula place, fixed_powerComparison place⟩

end LeanFormal.IUT.GeneralNormalizedNormFinalWiringFixed

end
