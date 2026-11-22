import LeanFormal.IUT.Foundations.AlgebraicGeometry.GeneralNormalizedNormBySpectralUniqueness
import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedNormSpectralBridge
import LeanFormal.IUT.Foundations.AlgebraicGeometry.BaseScalarValuationRelation

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# Final L0.4 assembly: general normalized norm formula

This file is the stable assembly of the L0.4 spectral-uniqueness route:

* the canonical absolute value extends the p-adic base norm;
* spectral uniqueness identifies it with the normalized spectral norm;
* the general normalized norm formula and logarithmic formula;
* the canonical power comparison;
* the base-scalar valuation identity.

No new residual is introduced; every declaration is a re-export of an actual
theorem from the spectral-uniqueness main file, the normalized bridge, or the
base-scalar valuation relation.  No fake norm formula.

No card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.GeneralNormalizedNormFinal

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.GeneralNormalizedNormBySpectralUniqueness
open LeanFormal.IUT.NormalizedNormSpectralBridge
open LeanFormal.IUT.BaseScalarValuationRelation

universe u

variable {F : Type u} [Field F] [NumberField F]
  (place : NumberField.FinitePlace F)

abbrev K : Type u := PadicScalarField place
abbrev N : Type u := NormalizedCompletion place
abbrev C : Type u := place.maximalIdeal.adicCompletion F

/-! ## Base-scalar identity -/

/-- The base-scalar valuation relation: for `q : PadicScalarField place`,
`Valued.v (algebraMap q : completion) = exp(-e*m)` for the actual DVR exponent
`m` of `q`.  This is the base-scalar input consumed by spectral uniqueness. -/
theorem baseScalarValuationIdentity
    (q : PadicScalarField place) (hq : q ≠ 0) :
    ∃ m : ℤ, q = (((LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime
        place).val : ℚ) : PadicScalarField place) ^ m *
      (algebraMap (ℤ_[(LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime
        place).val]) (PadicScalarField place)
        ((Classical.choose (BaseScalarValuationRelation.scalarDVRDecomposition
          place q hq) : ℤ_[(LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime
            place).val]) : ℤ_[(LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime
              place).val])) ∧
      (Valued.v (algebraMap (PadicScalarField place) (C place) q) :
        WithZero (Multiplicative ℤ)) =
        WithZero.exp (-(m * (BaseScalarValuationRelation.ramification place : ℤ))) :=
  BaseScalarValuationRelation.baseScalarValuationRelation place q hq

theorem normalizedNorm_eq_spectralNorm_final (x : N place) :
    ‖x‖ = spectralNorm (K place) (N place) x :=
  NormalizedNormSpectralBridge.normalizedNorm_eq_spectralNorm place x

/-! ## General formula and logarithm -/

theorem generalNormalizedNormFormula (x : N place) :
    ‖x‖ = (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^
      (-((nu place x : ℝ) /
        ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ))) :=
  NormalizedNormSpectralBridge.normalizedNorm_eq_formula place x

theorem generalNormalizedLogFormula (x : N place) :
    Real.log ‖x‖ = -(((nu place x : ℝ) *
      Real.log (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ)) /
      ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ)) :=
  NormalizedNormSpectralBridge.normalizedLogNorm_eq place x

theorem generalNormalizedLogFormula_apply
    (x : N place) :
    Real.log ‖x‖ = -(((nu place x : ℝ) *
      Real.log (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ)) /
      ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ)) :=
  generalNormalizedLogFormula place x

/-! ## Power comparison -/

theorem normalizedCanonicalPowerComparison_final
    (x : N place) (hx : x ≠ 0) :
    ‖x‖ ^ (relativeCompletionDegree (k := ℚ) place : ℕ) =
      ((Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^ nu place x)⁻¹ :=
  NormalizedNormSpectralBridge.normalizedCanonicalPowerComparison_normalized
    place x hx

theorem normalizedCanonicalPowerComparison_carrier
    (x : C place) (hx : x ≠ 0) :
    (spectralNorm (K place) (C place) x) ^
        (relativeCompletionDegree (k := ℚ) place : ℕ) =
      ((Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^ nu place x)⁻¹ :=
  GeneralNormalizedNormBySpectralUniqueness.normalizedCanonicalPowerComparison
    place x hx

/-! ## Packaged final chain -/

structure GeneralNormalizedNormBundle where
  baseScalarValuation : ∀ (q : PadicScalarField place), q ≠ 0 →
    ∃ m : ℤ, (Valued.v (algebraMap (PadicScalarField place) (C place) q) :
      WithZero (Multiplicative ℤ)) =
      WithZero.exp (-(m * (BaseScalarValuationRelation.ramification place : ℤ)))
  spectralBridge : ∀ x : N place, ‖x‖ = spectralNorm (K place) (N place) x
  normalizedFormula : ∀ x : N place,
    ‖x‖ = (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^
      (-((nu place x : ℝ) /
        ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ)))
  logFormula : ∀ x : N place,
    Real.log ‖x‖ = -(((nu place x : ℝ) *
      Real.log (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ)) /
      ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ))

noncomputable def generalNormalizedNormBundle :
    GeneralNormalizedNormBundle place :=
  { baseScalarValuation := by
      intro q hq
      exact (baseScalarValuationIdentity place q hq).imp
        (fun m hm => hm.2)
    spectralBridge := normalizedNorm_eq_spectralNorm_final place
    normalizedFormula := generalNormalizedNormFormula place
    logFormula := generalNormalizedLogFormula place }

theorem final_normalizedFormula :
    ∀ x : N place, ‖x‖ = (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^
      (-((nu place x : ℝ) /
        ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ))) :=
  generalNormalizedNormFormula place

theorem final_logFormula :
    ∀ x : N place, Real.log ‖x‖ =
      -(((nu place x : ℝ) * Real.log (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ)) /
        ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ)) :=
  generalNormalizedLogFormula place

theorem final_powerComparison :
    ∀ x : N place, x ≠ 0 →
      ‖x‖ ^ (relativeCompletionDegree (k := ℚ) place : ℕ) =
        ((Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^ nu place x)⁻¹ :=
  normalizedCanonicalPowerComparison_final place

end LeanFormal.IUT.GeneralNormalizedNormFinal

end
