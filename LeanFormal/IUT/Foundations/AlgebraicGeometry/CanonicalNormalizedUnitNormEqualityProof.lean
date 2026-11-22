import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedLogNormComparisonConcreteProof
import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedUniformizerNormProof
import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedUniformizerImageGenerator
import LeanFormal.IUT.Foundations.AlgebraicGeometry.UniformizerDVRDecomposition
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# Canonical/normalized unit norm equality

Goal: for every unit `x` of the normalized completion, the normalized norm of
`x` equals the canonical norm of `transportUnit x`.

Both norms are multiplicative, and the normalized ring equivalence identifies
their unit balls (`normalizedCompletion_norm_le_one_iff`).  A DVR decomposition
of `transportUnit x = π^m * u0` reduces the comparison to

* the uniformizer image norm `‖(ringEquiv).symm π‖ = ‖π‖`;
* the unit norm one for the normalized image of an actual integral unit.

The latter is proved from the unit-ball comparison; the former is the exact
uniformizer residual from `NormalizedUniformizerNormProof`.  No fake norm
equality is asserted.

No card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.CanonicalNormalizedUnitNormEqualityProof

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.CanonicalNormalizedNormEqualityProof
open LeanFormal.IUT.NormalizedUniformizerNormProof
open LeanFormal.IUT.NormalizedLogNormComparisonConcreteProof
open LeanFormal.IUT.UniformizerDVRDecomposition

universe u

local instance gaussianUnitNormEqualityIrreducibleFact :
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

/-- The actual uniformizer image. -/
noncomputable abbrev normalizedUniformizerImage : normalizedCompletion :=
  LeanFormal.IUT.NormalizedUniformizerNormProof.normalizedUniformizerImage

/-- Transport a normalized unit to the canonical field. -/
noncomputable def transportUnit (x : normalizedCompletionˣ) : completionFieldˣ :=
  Units.map (LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).toMonoidHom x

/-! ## Unit ball and integral-unit norm one -/

theorem normalizedCompletionRingEquiv_symm_le_one
    (x : completionField) :
    ‖(LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm x‖ ≤ 1 ↔
      ‖x‖ ≤ 1 :=
  (LeanFormal.IUT.normalizedCompletion_norm_le_one_iff concretePlace
    ((LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm x)).symm

theorem normalized_norm_transport_integralUnit_eq_one
    (u : (valuedInteger)ˣ) :
    ‖(LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm
      ((u.val).1 : completionField)‖ = 1 :=
by
  let e := LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace
  let z : normalizedCompletion := e.symm ((u.val).1 : completionField)
  have hz_le : ‖z‖ ≤ 1 :=
    (normalizedCompletionRingEquiv_symm_le_one ((u.val).1 : completionField)).mpr
      (by
        rw [← NormalizedLogNormComparison.norm_one_iff_valued_one]
        · exact norm_integralUnit_eq_one u
        · exact Units.ne_zero u)
  have hz_inv_le : ‖z⁻¹‖ ≤ 1 :=
  by
    have h := (normalizedCompletionRingEquiv_symm_le_one
      (((u⁻¹).val).1 : completionField)).mpr
      (by
        rw [← NormalizedLogNormComparison.norm_one_iff_valued_one]
        · exact norm_integralUnit_eq_one u⁻¹
        · exact Units.ne_zero u⁻¹)
    simpa [z, e] using h
  have hprod : ‖z‖ * ‖z⁻¹‖ = 1 :=
  by
    rw [← norm_mul, mul_inv_cancel, norm_one]
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr (by
    intro hz0
    exact Units.ne_zero u (by
      apply e.injective
      -- `e.symm` of the integral unit cannot be zero
      simpa [z, e, hz0] using (map_zero e)))
  nlinarith

/-! ## DVR reduction -/

/-- The canonical unit decomposes as `π^m * u0`; the normalized unit is the
corresponding product of the normalized image of `π` and the image of `u0`. -/
theorem normalized_unit_decomposition
    (x : normalizedCompletionˣ) {m : ℤ} {u0 : (valuedInteger)ˣ}
    (h : ((transportUnit x : completionFieldˣ) : completionField) =
      uniformizer ^ m * ((u0.val).1 : completionField)) :
    (x : normalizedCompletion) =
      normalizedUniformizerImage ^ m *
        (LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm
          ((u0.val).1 : completionField) :=
by
  apply (LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).injective
  rw [map_mul, map_zpow₀]
  simp [normalizedUniformizerImage, transportUnit] at h ⊢
  rw [h]

/-- Main reduction: uniformizer image equality implies the pointwise unit norm
equality. -/
theorem canonicalNormalizedUnitNormEquality_of_uniformizer
    (hpi : NormalizedUniformizerImageNormResidual) :
    CanonicalNormalizedUnitNormEquality :=
by
  intro x
  let y : completionFieldˣ := transportUnit x
  obtain ⟨m, u0, hdec⟩ := exists_uniformizer_dvr_decomposition y
  have hx := normalized_unit_decomposition x hdec
  have hdec' : (y : completionField) = uniformizer ^ m * ((u0.val).1 : completionField) :=
    hdec
  calc ‖(x : normalizedCompletion)‖
      = ‖normalizedUniformizerImage ^ m *
          (LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm
            ((u0.val).1 : completionField)‖ := by rw [hx]
    _ = ‖normalizedUniformizerImage‖ ^ m *
          ‖(LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm
            ((u0.val).1 : completionField)‖ := by
        rw [norm_mul, norm_zpow]
    _ = ‖uniformizer‖ ^ m * 1 := by
        rw [hpi, normalized_norm_transport_integralUnit_eq_one u0]
    _ = ‖(y : completionField)‖ := by
        rw [hdec', norm_mul, norm_zpow, norm_integralUnit_eq_one u0, mul_one]
    _ = ‖((transportUnit x : completionFieldˣ) : completionField)‖ := rfl

/-! ## Exact residual -/

/-- The exact residual is the normalized uniformizer image norm. -/
def CanonicalNormalizedUnitNormEqualityResidual : Prop :=
  NormalizedUniformizerImageNormResidual

theorem canonicalNormalizedUnitNormEquality_of_residual
    (h : CanonicalNormalizedUnitNormEqualityResidual) :
    CanonicalNormalizedUnitNormEquality :=
  canonicalNormalizedUnitNormEquality_of_uniformizer h


/-! ## Auxiliary norm and transport facts -/

theorem normalizedNormOnCompletion_mul (a b : normalizedCompletion) :
    ‖a * b‖ = ‖a‖ * ‖b‖ :=
  norm_mul a b

theorem normalizedNormOnCompletion_zpow (a : normalizedCompletion) (m : ℤ) :
    ‖a ^ m‖ = ‖a‖ ^ m :=
  norm_zpow a m

theorem transportUnit_apply (x : normalizedCompletionˣ) :
    ((transportUnit x : completionFieldˣ) : completionField) =
      (LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace)
        (x : normalizedCompletion) :=
  rfl

theorem transportUnit_injective :
    Function.Injective (transportUnit (place := concretePlace)) :=
by
  intro x y h
  have h' := congrArg (fun w : completionFieldˣ =>
    ((LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm
      (w : completionField))) h
  apply Units.ext
  simpa [transportUnit] using h'

theorem normalizedImage_pow_norm (m : ℤ) :
    ‖normalizedUniformizerImage ^ m‖ = ‖normalizedUniformizerImage‖ ^ m :=
  norm_zpow _ _

theorem normalized_norm_transport_unit_of_canonical
    (u : completionFieldˣ) :
    ‖(LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm
      (u : completionField)‖ = ‖(u : completionField)‖ →
      ‖(LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm
        (u : completionField)‖ = ‖(u : completionField)‖ :=
  fun h => h

theorem canonicalNormalizedUnitNormEquality_of_imageNorm
    (h : LeanFormal.IUT.NormalizedUniformizerNormProof.NormalizedUniformizerImageNormResidual) :
    CanonicalNormalizedUnitNormEquality :=
  canonicalNormalizedUnitNormEquality_of_uniformizer h

theorem canonicalNormalizedUnitNormEquality_of_generatorNorm
    (h : LeanFormal.IUT.NormalizedUniformizerImageGenerator.NormalizedGeneratorNormResidual) :
    CanonicalNormalizedUnitNormEquality :=
  canonicalNormalizedUnitNormEquality_of_uniformizer h

theorem canonicalNormalizedUnitNormEquality_of_exactResidual
    (h : LeanFormal.IUT.NormalizedGeneratorNormValue.NormalizedGeneratorNormExactResidual) :
    CanonicalNormalizedUnitNormEquality :=
  canonicalNormalizedUnitNormEquality_of_uniformizer
    (LeanFormal.IUT.NormalizedGeneratorNormValue.generatorNormResidual_of_exactResidual h)

theorem canonicalNormalizedUnitNormEqualityResidual_iff_imageNorm :
    CanonicalNormalizedUnitNormEqualityResidual ↔
      NormalizedUniformizerImageNormResidual :=
  Iff.rfl


/-! ## Consumer forms -/

theorem canonicalNormalizedUnitNormEquality_apply
    (h : CanonicalNormalizedUnitNormEquality) (x : normalizedCompletionˣ) :
    ‖(x : normalizedCompletion)‖ =
      ‖((transportUnit x : completionFieldˣ) : completionField)‖ :=
  h x

theorem canonicalNormalizedUnitNormEquality_apply_inv
    (h : CanonicalNormalizedUnitNormEquality) (x : normalizedCompletionˣ) :
    ‖((x⁻¹ : normalizedCompletionˣ) : normalizedCompletion)‖ =
      ‖(((transportUnit x)⁻¹ : completionFieldˣ) : completionField)‖ :=
by
  simpa [transportUnit] using h x⁻¹

theorem canonicalNormalizedUnitNormEquality_unit_norm_one
    (h : CanonicalNormalizedUnitNormEquality)
    (x : normalizedCompletionˣ)
    (hx : ‖((transportUnit x : completionFieldˣ) : completionField)‖ = 1) :
    ‖(x : normalizedCompletion)‖ = 1 :=
  (h x).trans hx

theorem normalized_unit_norm_eq_transport_norm_of_residual
    (h : CanonicalNormalizedUnitNormEqualityResidual)
    (x : normalizedCompletionˣ) :
    ‖(x : normalizedCompletion)‖ =
      ‖((transportUnit x : completionFieldˣ) : completionField)‖ :=
  canonicalNormalizedUnitNormEquality_of_residual h x

end LeanFormal.IUT.CanonicalNormalizedUnitNormEqualityProof

end
