import LeanFormal.IUT.Foundations.AlgebraicGeometry.GeneralNormalizedNormBySpectralUniqueness
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# Bridge from the normalized norm to the spectral norm

The normalized completion norm is the spectral norm over `PadicScalarField` by
construction.  This file states that bridge explicitly, transfers the formula
from the canonical completion carrier, and records the general normalized
formula and power comparison on `NormalizedCompletion place`.

No fake norm equality: the bridge is either definitional or an explicit
instance identification, not an asserted equality of unrelated norms.
-/

noncomputable section

namespace LeanFormal.IUT.NormalizedNormSpectralBridge

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.GeneralNormalizedNormBySpectralUniqueness

universe u

variable {F : Type u} [Field F] [NumberField F]
  (place : NumberField.FinitePlace F)

abbrev K : Type u := PadicScalarField place
abbrev N : Type u := NormalizedCompletion place
abbrev C : Type u := place.maximalIdeal.adicCompletion F

/-- The normalized norm is the spectral norm over the p-adic scalar field. -/
theorem normalizedNorm_eq_spectralNorm (x : N place) :
    ‖x‖ = spectralNorm (K place) (N place) x :=
  rfl

/-- The spectral norm on the normalized completion carrier is the same function
as on the canonical completion carrier (the underlying type is the same). -/
theorem spectralNorm_normalized_eq_canonical (x : N place) :
    spectralNorm (K place) (N place) x =
      spectralNorm (K place) (C place) x :=
  rfl

/-- The general normalized norm formula on the normalized completion. -/
theorem normalizedNorm_eq_formula (x : N place) :
    ‖x‖ = (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^
      (-((nu place x : ℝ) / ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ))) :=
by
  rw [normalizedNorm_eq_spectralNorm place x,
    spectralNorm_normalized_eq_canonical place x]
  exact GeneralNormalizedNormBySpectralUniqueness.spectralNorm_eq_formula place x

/-- The normalized logarithmic formula. -/
theorem normalizedLogNorm_eq (x : N place) :
    Real.log ‖x‖ = -(((nu place x : ℝ) *
      Real.log (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ)) /
      ((relativeCompletionDegree (k := ℚ) place : ℕ) : ℝ)) :=
by
  rw [normalizedNorm_eq_formula place x, Real.log_rpow (by positivity)]
  ring

/-- The normalized/canonical power comparison on the normalized carrier. -/
theorem normalizedCanonicalPowerComparison_normalized
    (x : N place) (hx : x ≠ 0) :
    ‖x‖ ^ (relativeCompletionDegree (k := ℚ) place : ℕ) =
      ((Ideal.absNorm place.maximalIdeal.asIdeal : ℝ) ^ nu place x)⁻¹ :=
by
  rw [normalizedNorm_eq_spectralNorm place x,
    spectralNorm_normalized_eq_canonical place x]
  exact GeneralNormalizedNormBySpectralUniqueness.normalizedCanonicalPowerComparison
    place x hx

end LeanFormal.IUT.NormalizedNormSpectralBridge

end
