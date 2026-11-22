import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedPrincipalIdealTransportProof
import LeanFormal.IUT.Foundations.AlgebraicGeometry.CanonicalNormalizedUnitNormEqualityFinal
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S1952Probe4

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NormalizedPrincipalIdealTransportProof
open LeanFormal.IUT.CanonicalNormalizedUnitNormEqualityFinal

local instance probeGaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance probeFivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

-- K is normalizedCompletion, defeq to concreteLogShellField.
example : concreteLogShellField = normalizedCompletion := rfl

theorem probePi_norm :
    ‖(normalizedUniformizerIntegral : normalizedIntegers) : normalizedCompletion‖ =
      (5 : ℝ)⁻¹ := by
  have h : ((normalizedUniformizerIntegral : normalizedIntegers) : normalizedCompletion) =
      (normalizedImageUnit : normalizedCompletion) := rfl
  rw [h]
  exact normalizedImageUnit_norm

theorem probePi_ne_zero : (normalizedUniformizerIntegral : normalizedIntegers) ≠ 0 := by
  intro h
  have hnorm := probePi_norm
  rw [h, Subring.coe_zero, norm_zero] at hnorm
  norm_num at hnorm

theorem probePi_irreducible :
    Irreducible (normalizedUniformizerIntegral : normalizedIntegers) := by
  letI : IsDiscreteValuationRing (Integers normalizedCompletion) :=
    isDiscreteValuationRingIntegers (K := normalizedCompletion) (p := 5)
  exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
    normalizedUniformizerIntegral probePi_ne_zero
    (normalizedMaximalIdeal_eq_span_uniformizer).symm

theorem probeFive_norm :
    ‖(5 : normalizedCompletion)‖ = (5 : ℝ)⁻¹ := by
  have h : (5 : normalizedCompletion) = (normalizedFiveUnit : normalizedCompletion) := by
    rw [normalizedFiveUnit]
    simp
  rw [h]
  exact normalizedFiveUnit_norm

theorem probeFive_associated_pi :
    Associated (5 : normalizedIntegers) normalizedUniformizerIntegral := by
  let π : normalizedCompletion := (normalizedUniformizerIntegral : normalizedCompletion)
  let q : normalizedCompletion := (5 : normalizedCompletion) / π
  have hπnorm : ‖π‖ = (5 : ℝ)⁻¹ := probePi_norm
  have h5norm : ‖(5 : normalizedCompletion)‖ = (5 : ℝ)⁻¹ := probeFive_norm
  have hπne : π ≠ 0 := by
    intro h
    rw [h, norm_zero] at hπnorm
    norm_num at hπnorm
  have hqnorm : ‖q‖ = 1 := by
    simp only [q, norm_div, h5norm, hπnorm, div_self]
    norm_num
  have hqinvnorm : ‖q⁻¹‖ = 1 := by
    rw [norm_inv, hqnorm, inv_one]
  let u : (normalizedIntegers)ˣ := unitOfNormOne ⟨q, by rw [hqnorm]; norm_num⟩
  have huval : ((u : normalizedIntegers) : normalizedCompletion) = q := rfl
  refine ⟨u, ?_⟩
  apply Subtype.ext
  change q * π = (5 : normalizedCompletion)
  rw [← huval]
  dsimp [q]
  field_simp [hπne]

theorem probeFive_irreducible : Irreducible (5 : normalizedIntegers) :=
  (probeFive_associated_pi.symm.irreducible_iff).mpr probePi_irreducible

theorem probeFive_irreducible_actual : Irreducible (5 : Integers concreteLogShellField) := by
  simpa [concreteLogShellField, normalizedCompletion] using probeFive_irreducible

end LeanFormal.IUT.XiFPaper.S1952Probe4
end