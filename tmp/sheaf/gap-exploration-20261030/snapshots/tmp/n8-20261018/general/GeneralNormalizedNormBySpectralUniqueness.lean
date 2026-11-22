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

theorem nu_add_ge_min (x y : L) :
    min (nu place x) (nu place y) ≤ nu place (x + y) :=
by
  by_cases hx : x = 0
  · subst hx; simp [nu]
  · by_cases hy : y = 0
    · subst hy; simp [nu]
    · by_cases hzero : x + y = 0
      · simp [nu, hzero]
      · have hvx : Valued.v x ≠ 0 :=
          fun h => hx ((Valued.v).map_eq_zero_iff.mp h)
        have hvy : Valued.v y ≠ 0 :=
          fun h => hy ((Valued.v).map_eq_zero_iff.mp h)
        have hvsum : Valued.v (x + y) ≠ 0 :=
          fun h => hzero ((Valued.v).map_eq_zero_iff.mp h)
        have hmap := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).map_add x y
        have hlog : WithZero.log (Valued.v (x + y)) ≤
            max (WithZero.log (Valued.v x)) (WithZero.log (Valued.v y)) :=
        by
          by_cases hxy : Valued.v x ≤ Valued.v y
          · have hmax : max (Valued.v x) (Valued.v y) = Valued.v y := max_eq_right hxy
            rw [hmax] at hmap
            exact (WithZero.log_le_log hvsum hvy).mpr hmap
          · have hmax : max (Valued.v x) (Valued.v y) = Valued.v x :=
              max_eq_left (le_of_not_ge hxy)
            rw [hmax] at hmap
            exact (WithZero.log_le_log hvsum hvx).mpr hmap
        simpa [nu, neg_max, max_neg, min_comm, max_comm] using neg_le_neg hlog
theorem max_neg_div_eq (a b : ℤ) :
    max (-(a : ℝ) / (d place : ℝ)) (-(b : ℝ) / (d place : ℝ)) =
      -(min a b : ℝ) / (d place : ℝ) :=
by
  have hd : (0 : ℝ) < (d place : ℝ) :=
    by exact_mod_cast relativeCompletionDegree_pos (k := ℚ) place
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left]
    · exact div_le_div_of_nonneg_right (by exact_mod_cast (neg_le_neg h)) hd.le
  · rw [min_eq_right h, max_eq_right]
    · exact div_le_div_of_nonneg_right (by exact_mod_cast (neg_le_neg h)) hd.le
theorem canonicalAbsValue_add_le_aux
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    (absNorm place) ^ (-(nu place (x + y) : ℝ) / (d place : ℝ)) ≤
      max ((absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ)))
        ((absNorm place) ^ (-(nu place y : ℝ) / (d place : ℝ))) :=
by
  have hnu := nu_add_ge_min place x y
  have hd : (0 : ℝ) < (d place : ℝ) :=
    by exact_mod_cast relativeCompletionDegree_pos (k := ℚ) place
  have hexp :
      -(nu place (x + y) : ℝ) / (d place : ℝ) ≤
        max (-(nu place x : ℝ) / (d place : ℝ))
          (-(nu place y : ℝ) / (d place : ℝ)) :=
  by
    rw [max_neg_div_eq place (nu place x) (nu place y)]
    have hdiv : (min (nu place x) (nu place y) : ℝ) / (d place : ℝ) ≤
        (nu place (x + y) : ℝ) / (d place : ℝ) :=
    by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hnu) hd.le
    exact neg_le_neg hdiv
  exact Real.rpow_le_rpow_left₀ (by positivity) (absNorm_gt_one place).le hexp

noncomputable def canonicalAbsValue : AbsoluteValue L ℝ where
  toFun x := if x = 0 then 0 else
    (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ))
  map_mul' x y := by
    by_cases hx : x = 0
    · subst hx; simp
    · by_cases hy : y = 0
      · subst hy; simp
      · have hxy : x * y ≠ 0 := mul_ne_zero hx hy
        simp [hx, hy, hxy]
        rw [map_mul, nu, WithZero.log_mul]
        · rw [WithZero.log_mul]
          · ring_nf
          · exact WithZero.exp_ne_zero _
        · exact WithZero.exp_ne_zero _
  nonneg' x := by
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx, Real.rpow_nonneg (by positivity) _]
  eq_zero' x := by
    constructor
    · intro hzero
      by_cases hx : x = 0
      · exact hx
      · simp [hx] at hzero
        have hpos : 0 < (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ)) :=
          Real.rpow_pos_of_pos (by positivity) _
        linarith
    · intro hx; subst hx; simp
  add_le' x y := by
    by_cases hx : x = 0
    · subst hx; simp
    · by_cases hy : y = 0
      · subst hy; simp
      · by_cases hxy : x + y = 0
        · subst hxy; simp
        · simp [hx, hy, hxy]
          exact canonicalAbsValue_add_le_aux place x y hx hy hxy

/-- The canonical absolute value extends the p-adic norm on the scalar field. -/
theorem canonicalAbsValue_extends (q : K) :
    canonicalAbsValue place (algebraMap K L q) = ‖q‖ :=
by
  by_cases hq : q = 0
  · subst hq
    simp [canonicalAbsValue]
  · obtain ⟨m, u, hdec, hval⟩ := baseScalarValuationRelation place q hq
    have hmap_ne : algebraMap K L q ≠ 0 :=
      fun h => hq ((algebraMap K L).injective (by simpa using h))
    simp only [canonicalAbsValue, if_neg hmap_ne]
    have hqnorm : ‖q‖ = (pNat place : ℝ) ^ (-m : ℤ) :=
    by
      rw [Padic.norm_eq_zpow_neg_valuation]
      rfl
    rw [hval]
    rw [show nu place (algebraMap K L q) = m * (e place : ℤ) from by
      unfold nu
      rw [hval, WithZero.log_exp]
      ring]
    rw [hqnorm, d_eq_e_mul_f]
    norm_num [absNorm]
/-! ## Spectral identification -/

theorem canonicalAbsValue_eq_spectralNorm (x : L) :
    canonicalAbsValue place x = spectralNorm K L x :=
  spectralNorm_unique_field_norm_ext (K := K) (L := L)
    (f := canonicalAbsValue place) (canonicalAbsValue_extends place) x

/-! ## Consequences -/

theorem spectralNorm_eq_formula (x : L) :
    spectralNorm K L x = (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ)) :=
  (canonicalAbsValue_eq_spectralNorm place x).symm

theorem normalizedCanonicalPowerComparison :
    ∀ x : L, x ≠ 0 →
      (spectralNorm K L x) ^ d place = (absNorm place ^ nu place x)⁻¹ :=
by
  intro x hx
  rw [spectralNorm_eq_formula place x]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  rw [show -(nu place x : ℝ) / (d place : ℝ) * (d place : ℕ) = -(nu place x : ℝ) from by
    field_simp [ne_of_gt (by exact_mod_cast relativeCompletionDegree_pos (k := ℚ) place : (0:ℝ) < _)]]
  rw [Real.rpow_neg (by positivity)]
  rw [Real.rpow_intCast]
  rw [inv_inv]

end LeanFormal.IUT.GeneralNormalizedNormBySpectralUniqueness

end