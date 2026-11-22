import LeanFormal.IUT.Foundations.AlgebraicGeometry.BaseNormCompatibilityProof
import LeanFormal.IUT.Foundations.AlgebraicGeometry.ClosedBallCompactness
import LeanFormal.IUT.Foundations.AlgebraicGeometry.UniformizerDVRDecomposition
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# Canonical vs normalized norm on the completion

Both norms have the same unit ball (`normalizedNormOnCompletion_le_one_iff`).
This file reduces their pointwise equality to the single uniformizer-value
comparison `normalizedNormOnCompletion π = ‖π‖`:

* multiplicativity and powers of the normalized norm are proved;
* every nonzero `x` is `π^m * u0` with `u0` an actual integral unit, and
  integral units have norm one for both norms;
* therefore equality at `π` implies equality everywhere.

The remaining uniformizer equality is not postulated: it is the explicit
residual `NormalizedUniformizerNormResidual`, equivalent to the missing
absolute-value extension uniqueness at the maximal ideal.  No fake instance.

No card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.CanonicalNormalizedNormEqualityProof

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.BaseNormCompatibilityProof
open LeanFormal.IUT.ClosedBallCompactness
open LeanFormal.IUT.UniformizerDVRDecomposition
open LeanFormal.IUT.LocalFieldIntegralUnits

universe u

local instance gaussianNormEqualityIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

local instance factFivePrime : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The canonical completion. -/
abbrev completionField : Type :=
  LeanFormal.IUT.BaseNormCompatibilityProof.completionField

/-- The actual valuation integer ring. -/
abbrev valuedInteger : Subring completionField :=
  LeanFormal.IUT.NormalizedLogNormComparison.valuedInteger

/-- The actual uniformizer. -/
noncomputable abbrev uniformizer : completionField :=
  LeanFormal.IUT.ClosedBallCompactness.uniformizer

/-- The uniformizer as a unit. -/
noncomputable def uniformizerUnit : completionFieldˣ :=
  Units.mk0 uniformizer (LeanFormal.IUT.UniformizerDVRDecomposition.concreteAdicUniformizer_ne_zero)

/-- An actual integral unit has valuation one. -/
theorem integralUnit_valued_eq_one (u : (valuedInteger)ˣ) :
    (Valued.v ((u.val).1 : completionField) : WithZero (Multiplicative ℤ)) = 1 := by
  let O : Subring completionField := valuedInteger
  have hunit : IsUnit (u.val : O) := Units.isUnit u
  have h := (Valuation.Integers.isUnit_iff_valuation_eq_one
    (v := Valued.v) (O := O) (F := completionField)
    (Valuation.integer.integers Valued.v)).mp hunit
  simpa [O, valuedInteger] using h

/-! ## Elementary properties of the normalized norm -/

theorem normalizedNormOnCompletion_mul (x y : completionField) :
    normalizedNormOnCompletion (x * y) =
      normalizedNormOnCompletion x * normalizedNormOnCompletion y :=
by
  unfold normalizedNormOnCompletion
  rw [map_mul, norm_mul]

theorem normalizedNormOnCompletion_pow (x : completionField) (n : ℕ) :
    normalizedNormOnCompletion (x ^ n) =
      normalizedNormOnCompletion x ^ n :=
by
  induction n with
  | zero => simp [normalizedNormOnCompletion]
  | succ n ih =>
      rw [pow_succ, normalizedNormOnCompletion_mul, ih, pow_succ]

theorem normalizedNormOnCompletion_pos {x : completionField} (hx : x ≠ 0) :
    0 < normalizedNormOnCompletion x :=
  norm_pos_iff.mpr (fun h => hx
    ((LeanFormal.IUT.normalizedCompletionRingEquiv concretePlace).symm.injective
      (by simpa [normalizedNormOnCompletion] using h)))

theorem normalizedNormOnCompletion_unit_eq_one
    (u : (valuedInteger)ˣ) :
    normalizedNormOnCompletion ((u.val).1 : completionField) = 1 :=
by
  haveI : ProperSpace completionField := properSpace_canonical
  have hle : normalizedNormOnCompletion ((u.val).1 : completionField) ≤ 1 :=
    (normalizedNormOnCompletion_le_one_iff _).mpr (by
      rw [← NormalizedLogNormComparison.norm_one_iff_valued_one]
      exact integralUnit_valued_eq_one u)
  have hinvle : normalizedNormOnCompletion ((u⁻¹).val).1 ≤ 1 :=
    (normalizedNormOnCompletion_le_one_iff _).mpr (by
      rw [← NormalizedLogNormComparison.norm_one_iff_valued_one]
      exact integralUnit_valued_eq_one u⁻¹)
  have hprod : normalizedNormOnCompletion ((u.val).1 : completionField) *
      normalizedNormOnCompletion ((u⁻¹).val).1 = 1 :=
  by
    rw [← normalizedNormOnCompletion_mul]
    congr 1
    rw [← Units.val_mul]
    simp
  have hpos : 0 < normalizedNormOnCompletion ((u.val).1 : completionField) :=
    normalizedNormOnCompletion_pos (Units.ne_zero u)
  nlinarith

/-! ## Reduction to the uniformizer -/

/-- The exact uniformizer-value comparison. -/
def NormalizedUniformizerNormResidual : Prop :=
  normalizedNormOnCompletion uniformizer = ‖uniformizer‖

theorem normalizedNormOnCompletion_uniformizer_pow
    (m : ℤ) :
    normalizedNormOnCompletion (uniformizer ^ m) =
      normalizedNormOnCompletion uniformizer ^ m :=
by
  -- zpow version of the power law, using the uniformizer unit
  let u : completionFieldˣ := uniformizerUnit
  have hm : (uniformizer ^ m) = (u ^ m : completionFieldˣ) := by
    ext; simp [u, uniformizerUnit]
  rw [hm]
  have h := congrArg normalizedNormOnCompletion (show
      ((u ^ m : completionFieldˣ) : completionField) =
        (u : completionField) ^ m from rfl)
  simpa [normalizedNormOnCompletion_pow] using h

/-- If the uniformizer values agree, a `π^m * u0` decomposition has the same
norm for both norms. -/
theorem norm_eq_of_decomposition
    (hpi : NormalizedUniformizerNormResidual)
    (m : ℤ) (u0 : (valuedInteger)ˣ) :
    normalizedNormOnCompletion
        (uniformizer ^ m * ((u0.val).1 : completionField)) =
      ‖uniformizer ^ m * ((u0.val).1 : completionField)‖ :=
by
  rw [normalizedNormOnCompletion_mul, normalizedNormOnCompletion_unit_eq_one]
  rw [normalizedNormOnCompletion_uniformizer_pow]
  rw [norm_mul]
  rw [NormalizedLogNormComparison.norm_one_iff_valued_one]
  · rw [hpi]
    rw [mul_one, mul_one]
  · exact (by
      have : ((u0.val).1 : completionField) ≠ 0 := Units.ne_zero u0
      exact this)
  · exact integralUnit_valued_eq_one u0

/-- If the uniformizer values agree, canonical and normalized norms agree on
every nonzero element, by DVR decomposition. -/
theorem normalizedNorm_eq_norm_of_uniformizer
    (hpi : NormalizedUniformizerNormResidual) {x : completionField} (hx : x ≠ 0) :
    normalizedNormOnCompletion x = ‖x‖ :=
by
  let ux : completionFieldˣ := Units.mk0 x hx
  obtain ⟨m, u0, hdec⟩ := exists_uniformizer_dvr_decomposition ux
  have hxdec : x = uniformizer ^ m * ((u0.val).1 : completionField) := by
    simpa [ux, uniformizer] using hdec
  rw [hxdec]
  exact norm_eq_of_decomposition hpi m u0

/-- Main reduction: uniformizer equality implies the full canonical/normalized
norm equality. -/
theorem canonicalNormalizedNormEquality_of_uniformizer
    (hpi : NormalizedUniformizerNormResidual) :
    CanonicalNormalizedNormEquality :=
by
  intro x
  by_cases hx : x = 0
  · subst x
    simp [normalizedNormOnCompletion]
  · exact (normalizedNorm_eq_norm_of_uniformizer hpi hx).symm

/-! ## Exact residual variants -/

/-- The uniformizer residual is equivalent to the full norm equality together
with equality at the uniformizer (the nontrivial direction is the main
reduction above). -/
theorem normalizedUniformizerNormResidual_iff
    (h : CanonicalNormalizedNormEquality) :
    NormalizedUniformizerNormResidual :=
  h uniformizer

theorem canonicalNormalizedNormEquality_iff_uniformizer
    (hpi : NormalizedUniformizerNormResidual) :
    CanonicalNormalizedNormEquality :=
  canonicalNormalizedNormEquality_of_uniformizer hpi

/-- The uniformizer residual is the exact remaining maximal-ideal/uniformizer
valuation equality; it is recorded, not inhabited. -/
def MaximalIdealUniformizerValuationResidual : Prop :=
  NormalizedUniformizerNormResidual


/-! ## Consequences of the reduction -/

/-- The canonical norm of an actual integral unit is one. -/
theorem norm_integralUnit_eq_one (u : (valuedInteger)ˣ) :
    ‖((u.val).1 : completionField)‖ = 1 :=
by
  rw [NormalizedLogNormComparison.norm_one_iff_valued_one]
  · exact integralUnit_valued_eq_one u
  · exact Units.ne_zero u

theorem normalizedNormOnCompletion_inv (x : completionField) :
    normalizedNormOnCompletion x⁻¹ = (normalizedNormOnCompletion x)⁻¹ :=
by
  unfold normalizedNormOnCompletion
  rw [map_inv₀, norm_inv]

theorem normalizedNormOnCompletion_zpow (x : completionField) (m : ℤ) :
    normalizedNormOnCompletion (x ^ m) =
      normalizedNormOnCompletion x ^ m :=
by
  cases m with
  | ofNat n => simpa using normalizedNormOnCompletion_pow x n
  | negSucc n =>
      rw [zpow_negSucc, normalizedNormOnCompletion_inv,
        normalizedNormOnCompletion_pow]

/-- Uniformizer equality is exactly the missing maximal-ideal valuation
equality at the chosen local parameter. -/
theorem uniformizerResidual_iff_norm
    (h : normalizedNormOnCompletion uniformizer = ‖uniformizer‖) :
    NormalizedUniformizerNormResidual :=
  h

theorem norm_uniformizer_eq_inv_five :
    ‖uniformizer‖ = (5 : ℝ)⁻¹ :=
by
  have h := NormalizedLogNormComparison.norm_eq_absNorm_zpow concretePlace
    uniformizer (LeanFormal.IUT.UniformizerDVRDecomposition.concreteAdicUniformizer_ne_zero)
  rw [h]
  -- the valuation exponent of the actual uniformizer is -1
  have hv : (Valued.v uniformizer : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-1 : ℤ) :=
    LeanFormal.IUT.UniformizerDVRDecomposition.concreteAdicUniformizer_valued
  have hlog : Multiplicative.toAdd (WithZero.unzero
      (LeanFormal.IUT.NumberFieldFinitePlace.valuation_ne_zero_of_ne_zero
        concretePlace uniformizer
        (LeanFormal.IUT.UniformizerDVRDecomposition.concreteAdicUniformizer_ne_zero))) = -1 :=
  by
    apply WithZero.exp_inj.mp
    rw [WithZero.exp_log (LeanFormal.IUT.NumberFieldFinitePlace.valuation_ne_zero_of_ne_zero
      concretePlace uniformizer
      (LeanFormal.IUT.UniformizerDVRDecomposition.concreteAdicUniformizer_ne_zero)), hv]
  rw [hlog]
  rw [concretePlace_upper_absNorm]
  norm_num

/-- The residual uniformizer equality is equivalent to the normalized norm of
the actual uniformizer being `1/5`. -/
theorem normalizedUniformizerNormResidual_iff_inv_five :
    NormalizedUniformizerNormResidual ↔
      normalizedNormOnCompletion uniformizer = (5 : ℝ)⁻¹ :=
by
  rw [NormalizedUniformizerNormResidual, norm_uniformizer_eq_inv_five]

end LeanFormal.IUT.CanonicalNormalizedNormEqualityProof

end
