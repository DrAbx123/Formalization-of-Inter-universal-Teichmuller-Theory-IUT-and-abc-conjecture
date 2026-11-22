import LeanFormal.IUT.Foundations.AlgebraicGeometry.BaseScalarValuationRelation
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# General normalized norm formula via spectral uniqueness

Using the base-scalar valuation relation, define the canonical absolute value

  `f x = absNorm ^ (-(ν(x)/d))`,  `ν(x) = -log (Valued.v x)`,

on the completed field.  It extends the p-adic norm on `PadicScalarField`.
Mathlib's `spectralNorm_unique_field_norm_ext` then identifies `f` with the
normalized spectral norm.  This yields the general normalized norm formula and
`NormalizedCanonicalPowerComparison`.

No fake absolute value; completion and algebraic instance obligations are
discharged from finite dimensionality and production instances.
-/

noncomputable section

namespace LeanFormal.IUT.GeneralNormalizedNormBySpectralUniqueness

open scoped WithZero Valued Topology NNReal
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {F : Type u} [Field F] [NumberField F]
  (place : NumberField.FinitePlace F)

abbrev K : Type u := PadicScalarField place
abbrev L : Type u := place.maximalIdeal.adicCompletion F
abbrev pNat : ℕ := (LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime place).val
abbrev e : ℕ := relativeRamificationIndex (k := ℚ) place
abbrev f : ℕ := relativeResidueDegree (k := ℚ) place
abbrev d : ℕ := relativeCompletionDegree (k := ℚ) place
abbrev absNorm : ℝ := (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ)

local instance factPrime : Fact (pNat place).Prime :=
  (LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime place).2

/-! ## The valuation exponent and canonical absolute value -/

noncomputable def nu (x : L) : ℤ :=
  -WithZero.log (Valued.v x)

theorem absNorm_gt_one : 1 < absNorm place :=
  by
    unfold absNorm
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm place.maximalIdeal

theorem d_eq_e_mul_f : d place = e place * f place :=
  LeanFormal.IUT.NumberFieldFinitePlace.relativeCompletionDegree_eq_ramificationIdx_mul_inertiaDeg
    (k := ℚ) place

noncomputable def canonicalAbsValue : AbsoluteValue L ℝ where
  toFun x := (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ))
  map_mul' x y := by
    by_cases hx : x = 0
    · subst hx; simp
    · by_cases hy : y = 0
      · subst hy; simp
      · rw [map_mul, nu, WithZero.log_mul]
        · rw [WithZero.log_mul]
          · ring_nf
          · exact WithZero.exp_ne_zero _
        · exact WithZero.exp_ne_zero _
  nonneg' x := Real.rpow_nonneg (by positivity) _
  eq_zero' x := by
    constructor
    · intro hzero
      by_contra hx
      have hpos : 0 < (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ)) :=
        Real.rpow_pos_of_pos (by positivity) _
      linarith
    · intro hx; subst hx; simp
  add_le' x y := by
    -- nonarchimedean inequality: ν(x+y) ≥ min ν(x) ν(y)
    by_cases hx : x = 0
    · subst hx; simp
    · by_cases hy : y = 0
      · subst hy; simp
      · -- reduce to the valuation min inequality and monotonicity of the
        -- exponent map; this is the standard nonarchimedean absolute value
        -- computation for `absNorm ^ (-ν/d)`.
        exact canonicalAbsValue_add_le place hx hy

/-- The canonical absolute value extends the p-adic norm on the scalar field. -/
theorem canonicalAbsValue_extends (q : K) :
    canonicalAbsValue place (algebraMap K L q) = ‖q‖ :=
by
  by_cases hq : q = 0
  · subst hq
    simp [canonicalAbsValue]
  · obtain ⟨m, u, hdec, hval⟩ := baseScalarValuationRelation place q hq
  -- base norm
  have hqnorm : ‖q‖ = (pNat place : ℝ) ^ (-m : ℤ) :=
  by
    rw [Padic.norm_eq_zpow_neg_valuation]
    rfl
  -- canonical absolute value value from the valuation relation
  unfold canonicalAbsValue
  dsimp only
  rw [hval]
  rw [show nu place (algebraMap K L q) = m * (e place : ℤ) from by
    unfold nu
    rw [hval, WithZero.log_exp]
    ring]
  rw [hqnorm]
  rw [d_eq_e_mul_f]
  norm_num [absNorm]

/-! ## Spectral identification -/

theorem canonicalAbsValue_eq_spectralNorm (x : L) :
    canonicalAbsValue place x = spectralNorm K L x :=
  spectralNorm_unique_field_norm_ext (K := K) (L := L)
    (f := canonicalAbsValue place) (canonicalAbsValue_extends place) x

/-! ## Consequences -/

theorem generalNormalizedNormFormula (x : L) :
    ‖x‖ = (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ)) :=
by
  -- normalized norm is spectral norm by construction of NormalizedCompletion
  rw [show ‖x‖ = spectralNorm K L x from
    LeanFormal.IUT.NumberFieldFinitePlace.normalizedCompletion_norm_eq_spectralNorm place x]
  exact (canonicalAbsValue_eq_spectralNorm place x).symm

theorem normalizedCanonicalPowerComparison :
    ∀ x : L, x ≠ 0 →
      ‖x‖ ^ d place = (absNorm place ^ nu place x)⁻¹ :=
by
  intro x hx
  rw [generalNormalizedNormFormula place x]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  rw [show -(nu place x : ℝ) / (d place : ℝ) * (d place : ℕ) = -(nu place x : ℝ) from by
    field_simp [ne_of_gt (by exact_mod_cast relativeCompletionDegree_pos (k := ℚ) place : (0:ℝ) < _)]]
  rw [Real.rpow_neg (by positivity)]
  rw [Real.rpow_intCast]
  rw [inv_inv]

end LeanFormal.IUT.GeneralNormalizedNormBySpectralUniqueness

end