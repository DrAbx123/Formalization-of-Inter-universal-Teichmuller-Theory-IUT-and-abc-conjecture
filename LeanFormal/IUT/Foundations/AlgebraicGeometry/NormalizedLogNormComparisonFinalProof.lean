import LeanFormal.IUT.Foundations.AlgebraicGeometry.MaximalIdealPrincipalIdealExponentProof
import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedLogNormComparisonConcreteProof
import LeanFormal.IUT.Foundations.AlgebraicGeometry.CanonicalNormalizedUnitNormEqualityProof
import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedUniformizerNormProof
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalIdealValuation

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# Final reduction of the concrete normalized log-norm formula

The remaining production statement is

  `Example36.NormalizedLogNormComparison concretePlace`.

Using the now-proved normalized generator valuation exponent (`= 1`), this file
proves the valuation-exponent comparison

  `completionValuationExponent place x = -WithZero.log (Valued.v (transport x))`

for every normalized unit, via the DVR decomposition of the transported
canonical unit.  Consequently the logarithmic norm formula reduces to the
single pointwise spectral equality

  `CanonicalNormalizedUnitNormEquality`.

Equivalently the only remaining statement is the normalized norm of the
maximal-ideal generator (`1/5`).  No fake norm or valuation formula is asserted.

No card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.NormalizedLogNormComparisonFinalProof

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.MaximalIdealPrincipalIdealExponentProof
open LeanFormal.IUT.NormalizedLogNormComparisonConcreteProof
open LeanFormal.IUT.CanonicalNormalizedUnitNormEqualityProof
open LeanFormal.IUT.NormalizedUniformizerNormProof
open LeanFormal.IUT.UniformizerDVRDecomposition
open LeanFormal.IUT.LocalFieldIntegralUnits

universe u

local instance gaussianFinalLogNormIrreducibleFact :
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

/-- The actual valuation integer ring. -/
abbrev valuedInteger : Subring completionField :=
  LeanFormal.IUT.NormalizedLogNormComparison.valuedInteger

/-- The normalized image unit. -/
noncomputable def normalizedImageUnit : normalizedCompletionˣ :=
  Units.mk0 normalizedUniformizerImage
    (LeanFormal.IUT.NormalizedUniformizerNormProof.normalizedUniformizerImage_ne_zero)

/-- Transport a normalized unit to the canonical field. -/
noncomputable def transportUnit (x : normalizedCompletionˣ) : completionFieldˣ :=
  Units.map (LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).toMonoidHom x

/-! ## Exponent of the normalized image -/

theorem normalizedImageUnit_exponent :
    completionValuationExponent concretePlace.maximalIdeal normalizedImageUnit = 1 :=
  normalizedGeneratorValuationExponentInput_holds

theorem normalizedImageUnit_transport :
    ((transportUnit normalizedImageUnit : completionFieldˣ) : completionField) =
      LeanFormal.IUT.ClosedBallCompactness.uniformizer :=
  rfl

/-! ## Exponent of the normalized image of an integral unit -/

noncomputable def normalizedIntegralUnit (u : (valuedInteger)ˣ) :
    normalizedCompletionˣ :=
  Units.map (LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm.toMonoidHom u

theorem normalizedIntegralUnit_exponent_zero (u : (valuedInteger)ˣ) :
    completionValuationExponent concretePlace.maximalIdeal
      (normalizedIntegralUnit u) = 0 :=
by
  -- normalized integral units are actual integral units, hence exponent zero
  rw [completionValuationExponent_eq_zero_iff_mem_integralUnits]
  exact (normalizedIntegralUnit u).property

/-! ## DVR decomposition of normalized units -/

theorem normalizedUnit_decomposition
    (x : normalizedCompletionˣ) {m : ℤ} {u0 : (valuedInteger)ˣ}
    (h : ((transportUnit x : completionFieldˣ) : completionField) =
      uniformizer ^ m * ((u0.val).1 : completionField)) :
    (x : normalizedCompletion) =
      (normalizedImageUnit : normalizedCompletion) ^ m *
        ((normalizedIntegralUnit u0 : normalizedCompletionˣ) : normalizedCompletion) :=
by
  apply (LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).injective
  rw [map_mul, map_zpow₀]
  simp [normalizedImageUnit, normalizedIntegralUnit, transportUnit] at h ⊢
  rw [h]

/-! ## Valuation-exponent comparison -/

theorem normalizedValueExponentComparison_holds :
    NormalizedValueExponentComparison :=
by
  intro x
  let y : completionFieldˣ := transportUnit x
  obtain ⟨m, u0, hdec⟩ := exists_uniformizer_dvr_decomposition y
  have hx := normalizedUnit_decomposition x hdec
  -- normalized exponent of x
  have hxexp : completionValuationExponent concretePlace.maximalIdeal x = m :=
  by
    rw [show (x : normalizedCompletion) =
      (normalizedImageUnit : normalizedCompletion) ^ m *
        ((normalizedIntegralUnit u0 : normalizedCompletionˣ) : normalizedCompletion) from hx]
    rw [completionValuationExponent_mul, completionValuationExponent_pow]
    have hpow : completionValuationExponent concretePlace.maximalIdeal
        (normalizedImageUnit ^ m) = m := by
      rw [completionValuationExponent_pow]
      rw [normalizedImageUnit_exponent]
      simp
    rw [hpow, normalizedIntegralUnit_exponent_zero]
    ring
  -- canonical valuation of the transported unit
  have hyval : -WithZero.log (Valued.v ((transportUnit x : completionFieldˣ) : completionField)) =
      (m : ℤ) :=
  by
    rw [hdec]
    rw [map_mul, map_zpow₀]
    rw [show (Valued.v (uniformizer : completionField) : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-1) from LeanFormal.IUT.UniformizerDVRDecomposition.concreteAdicUniformizer_valued]
    rw [LeanFormal.IUT.CanonicalNormalizedNormEqualityProof.integralUnit_valued_eq_one u0]
    rw [WithZero.log_mul, WithZero.log_exp, WithZero.log_one]
    · ring
    · simp
  rw [hxexp, hyval]

/-! ## Final reduction -/

theorem normalizedLogNormComparison_of_unitNormEquality
    (hnorm : CanonicalNormalizedUnitNormEquality) :
    Example36.NormalizedLogNormComparison concretePlace :=
  normalizedLogNormComparison_of_unit_norm_and_exponent
    hnorm normalizedValueExponentComparison_holds

/-- The exact remaining spectral equality. -/
def NormalizedLogNormSpectralResidual : Prop :=
  CanonicalNormalizedUnitNormEquality

theorem normalizedLogNormComparison_of_spectralResidual
    (h : NormalizedLogNormSpectralResidual) :
    Example36.NormalizedLogNormComparison concretePlace :=
  normalizedLogNormComparison_of_unitNormEquality h

theorem normalizedLogNormComparison_of_uniformizerNormResidual
    (h : NormalizedUniformizerImageNormResidual) :
    Example36.NormalizedLogNormComparison concretePlace :=
  normalizedLogNormComparison_of_unitNormEquality
    (canonicalNormalizedUnitNormEquality_of_uniformizer h)

/-! ## Exact status -/

theorem normalizedLogNormComparisonResidual_iff :
    NormalizedLogNormSpectralResidual ↔ CanonicalNormalizedUnitNormEquality :=
  Iff.rfl

theorem normalizedLogNormComparison_of_generatorNorm
    (h : LeanFormal.IUT.NormalizedUniformizerImageGenerator.NormalizedGeneratorNormResidual) :
    Example36.NormalizedLogNormComparison concretePlace :=
  normalizedLogNormComparison_of_unitNormEquality
    (canonicalNormalizedUnitNormEquality_of_generatorNorm h)


/-! ## Auxiliary zpow/additivity facts -/

theorem completionValuationExponent_zpow
    (x : normalizedCompletionˣ) (m : ℤ) :
    completionValuationExponent concretePlace.maximalIdeal (x ^ m) =
      m * completionValuationExponent concretePlace.maximalIdeal x :=
by
  cases m with
  | ofNat n =>
      simpa using completionValuationExponent_pow x n
  | negSucc n =>
      rw [zpow_negSucc, completionValuationExponent_pow,
        completionValuationExponent_eq_zero_iff_mem_integralUnits]
      · ring
      · -- the inverse of a unit is an integral unit exactly when the unit is
        exact (x ^ (n + 1)).property

theorem normalizedImageUnit_pow_exponent (m : ℤ) :
    completionValuationExponent concretePlace.maximalIdeal
      (normalizedImageUnit ^ m) = m :=
by
  rw [completionValuationExponent_zpow, normalizedImageUnit_exponent]
  simp

theorem normalizedIntegralUnit_mul_exponent
    (u : (valuedInteger)ˣ) (x : normalizedCompletionˣ) :
    completionValuationExponent concretePlace.maximalIdeal
      (normalizedIntegralUnit u * x) =
      completionValuationExponent concretePlace.maximalIdeal x :=
by
  rw [completionValuationExponent_mul, normalizedIntegralUnit_exponent_zero]
  ring

/-! ## Projections of the exact residual -/

theorem normalizedLogNormSpectralResidual_unitNorm
    (h : NormalizedLogNormSpectralResidual) :
    CanonicalNormalizedUnitNormEquality :=
  h

theorem normalizedLogNormComparison_of_spectralResidual_unconditional
    (h : NormalizedLogNormSpectralResidual) :
    Example36.NormalizedLogNormComparison concretePlace :=
  normalizedLogNormComparison_of_spectralResidual h

theorem normalizedLogNormComparison_of_exactGeneratorResidual
    (h : LeanFormal.IUT.NormalizedGeneratorNormValue.NormalizedGeneratorNormExactResidual) :
    Example36.NormalizedLogNormComparison concretePlace :=
by
  let hgen := LeanFormal.IUT.NormalizedGeneratorNormValue.generatorNormResidual_of_exactResidual h
  exact normalizedLogNormComparison_of_generatorNorm hgen


/-! ## Consumer chain -/

theorem normalizedGeneratorNormResidual_of_spectralResidual
    (h : NormalizedLogNormSpectralResidual) :
    LeanFormal.IUT.NormalizedGeneratorNormValue.NormalizedLogNormResidual :=
  normalizedLogNormComparison_of_spectralResidual h

theorem normalizedGeneratorNorm_of_spectralResidual
    (h : NormalizedLogNormSpectralResidual) :
    LeanFormal.IUT.NormalizedUniformizerImageGenerator.NormalizedGeneratorNormResidual :=
  LeanFormal.IUT.NormalizedGeneratorNormValue.generatorNormResidual_of_logNorm_and_valuation
    (normalizedLogNormComparison_of_spectralResidual h)
    normalizedGeneratorValuationExponentInput_holds

theorem canonicalNormalizedNormEquality_of_spectralResidual
    (h : NormalizedLogNormSpectralResidual) :
    CanonicalNormalizedNormEquality :=
  LeanFormal.IUT.NormalizedGeneratorNormValue.canonicalNormalizedNormEquality_of_logNorm_and_valuation
    (normalizedLogNormComparison_of_spectralResidual h)
    normalizedGeneratorValuationExponentInput_holds

/-- With the spectral unit norm equality supplied, the normalized generator
norm is `1/5` and the canonical/normalized norm equality closes. -/
theorem normalizedImageNormResidual_of_spectralResidual
    (h : NormalizedLogNormSpectralResidual) :
    LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerImageNormResidual :=
  LeanFormal.IUT.NormalizedGeneratorNormValue.generatorNormResidual_of_logNorm_and_valuation
    (normalizedLogNormComparison_of_spectralResidual h)
    normalizedGeneratorValuationExponentInput_holds

theorem normalizedLogNormSpectralResidual_iff :
    NormalizedLogNormSpectralResidual ↔ CanonicalNormalizedUnitNormEquality :=
  Iff.rfl

theorem normalizedLogNormComparison_consumer
    (h : NormalizedLogNormSpectralResidual) :
    Example36.NormalizedLogNormComparison concretePlace :=
  normalizedLogNormComparison_of_spectralResidual h
end LeanFormal.IUT.NormalizedLogNormComparisonFinalProof

end