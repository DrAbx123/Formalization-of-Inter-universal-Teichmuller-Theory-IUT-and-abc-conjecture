import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionNormFormula
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

/-!
# S1448: route E, the general normalized norm formula

This file records the route-E repair of the general normalized norm formula, conditional on the exact scalar-extension input:

* the absolute value is defined with a zero branch, so its value at 0 is 0 and
  not the positive number absNorm ^ 0 = 1;
* the corrected function is proved to be a genuine AbsoluteValue;
* the degree identity d = e * f is used to rewrite the normalized exponent
  -nu / d as -nu / e in the residue-norm base p;
* the still-exact scalar-extension input is isolated as the named proposition
  ScalarExtensionCompatibility, and the spectral identification is derived
  from it without asserting any unproved equality of norms.

The scalar-extension proposition is not asserted.  The file consequently does
not claim the unconditional normalized norm formula.  It supplies the corrected
zero branch and the degree-formula reduction, and states exactly what remains.

No sorry, no axiom, no fake norm equality.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1448ReportENormalizedNormActual

open scoped WithZero Valued Topology
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {F : Type u} [Field F] [NumberField F] (place : NumberField.FinitePlace F)

abbrev K (place : NumberField.FinitePlace F) : Type := PadicScalarField place

abbrev N (place : NumberField.FinitePlace F) : Type u := NormalizedCompletion place

local instance decidableEqN : DecidableEq (N place) := Classical.decEq (N place)

local instance valuedN : Valued (N place) (WithZero (Multiplicative ℤ)) := by
  change Valued (Completion place) (WithZero (Multiplicative ℤ))
  infer_instance

noncomputable abbrev pNat (place : NumberField.FinitePlace F) : ℕ :=
  (completionRationalPrime place).val

abbrev e (place : NumberField.FinitePlace F) : ℕ :=
  relativeRamificationIndex (k := ℚ) place

abbrev f (place : NumberField.FinitePlace F) : ℕ :=
  relativeResidueDegree (k := ℚ) place

abbrev d (place : NumberField.FinitePlace F) : ℕ :=
  relativeCompletionDegree (k := ℚ) place

abbrev absNorm (place : NumberField.FinitePlace F) : ℝ :=
  (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ)

theorem absNorm_gt_one : 1 < absNorm place := by
  unfold absNorm
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm place.maximalIdeal

theorem absNorm_pos : 0 < absNorm place :=
  zero_lt_one.trans (absNorm_gt_one place)

theorem d_eq_e_mul_f : d place = e place * f place := rfl

theorem d_pos : 0 < d place :=
  relativeCompletionDegree_pos (k := ℚ) place

theorem e_pos : 0 < e place :=
  Nat.pos_of_ne_zero (relativeRamificationIndex_ne_zero (k := ℚ) place)

theorem f_pos : 0 < f place :=
  Nat.pos_of_ne_zero (relativeResidueDegree_ne_zero (k := ℚ) place)

noncomputable def nu (x : N place) : ℤ :=
  -WithZero.log (Valued.v x)

theorem valued_ne_zero_of_ne_zero {x : N place} (hx : x ≠ 0) :
    (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := by
  intro h
  exact hx (((Valued.v : Valuation (N place) (WithZero (Multiplicative ℤ))).map_eq_zero_iff).mp h)

@[simp] theorem nu_zero : nu place 0 = 0 := by
  simp [nu]

theorem nu_mul {x y : N place} (hx : x ≠ 0) (hy : y ≠ 0) :
    nu place (x * y) = nu place x + nu place y := by
  have hvx := valued_ne_zero_of_ne_zero place hx
  have hvy := valued_ne_zero_of_ne_zero place hy
  unfold nu
  rw [map_mul, WithZero.log_mul hvx hvy]
  ring

theorem nu_add_ge_min_of_add_ne_zero {x y : N place}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (nu place x) (nu place y) ≤ nu place (x + y) := by
  have hvx := valued_ne_zero_of_ne_zero place hx
  have hvy := valued_ne_zero_of_ne_zero place hy
  have hvsum := valued_ne_zero_of_ne_zero place hxy
  have hmap := (Valued.v : Valuation (N place) (WithZero (Multiplicative ℤ))).map_add x y
  have hlog : WithZero.log (Valued.v (x + y)) ≤
      max (WithZero.log (Valued.v x)) (WithZero.log (Valued.v y)) := by
    by_cases hle : Valued.v x ≤ Valued.v y
    · rw [max_eq_right hle] at hmap
      exact le_trans ((WithZero.log_le_log hvsum hvy).mpr hmap) (le_max_right _ _)
    · rw [max_eq_left (le_of_not_ge hle)] at hmap
      exact le_trans ((WithZero.log_le_log hvsum hvx).mpr hmap) (le_max_left _ _)
  unfold nu
  rw [min_neg_neg]
  exact neg_le_neg hlog

noncomputable def canonicalAbsValueFun (x : N place) : ℝ :=
  if x = 0 then 0 else
    (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ))

@[simp] theorem canonicalAbsValueFun_zero : canonicalAbsValueFun place 0 = 0 := by
  simp [canonicalAbsValueFun]

theorem canonicalAbsValueFun_of_ne {x : N place} (hx : x ≠ 0) :
    canonicalAbsValueFun place x =
      (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ)) := by
  simp [canonicalAbsValueFun, hx]

theorem canonicalAbsValueFun_nonneg (x : N place) : 0 ≤ canonicalAbsValueFun place x := by
  by_cases hx : x = 0
  · simp [canonicalAbsValueFun, hx]
  · rw [canonicalAbsValueFun_of_ne place hx]
    exact Real.rpow_nonneg (le_of_lt (absNorm_pos place)) _

theorem canonicalAbsValueFun_eq_zero_iff (x : N place) :
    canonicalAbsValueFun place x = 0 ↔ x = 0 := by
  constructor
  · intro hzero
    by_contra hx
    rw [canonicalAbsValueFun_of_ne place hx] at hzero
    have hpos : 0 < (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ)) :=
      Real.rpow_pos_of_pos (absNorm_pos place) _
    linarith
  · rintro rfl
    simp

theorem canonicalAbsValueFun_mul (x y : N place) :
    canonicalAbsValueFun place (x * y) =
      canonicalAbsValueFun place x * canonicalAbsValueFun place y := by
  by_cases hx : x = 0
  · subst hx; simp [canonicalAbsValueFun]
  · by_cases hy : y = 0
    · subst hy; simp [canonicalAbsValueFun]
    · have hxy : x * y ≠ 0 := mul_ne_zero hx hy
      rw [canonicalAbsValueFun_of_ne place hxy,
        canonicalAbsValueFun_of_ne place hx,
        canonicalAbsValueFun_of_ne place hy,
        nu_mul place hx hy]
      rw [← Real.rpow_add (absNorm_pos place)]
      congr 1
      field_simp [ne_of_gt (d_pos place)]
      push_cast
      ring

theorem rpow_exponent_le_max (a b c : ℤ) (h : min a b ≤ c) :
    (absNorm place) ^ (-(c : ℝ) / (d place : ℝ)) ≤
      max ((absNorm place) ^ (-(a : ℝ) / (d place : ℝ)))
        ((absNorm place) ^ (-(b : ℝ) / (d place : ℝ))) := by
  have hd : (0 : ℝ) < (d place : ℝ) := by exact_mod_cast d_pos place
  have hmin_real : min (a : ℝ) (b : ℝ) = (min a b : ℝ) := by
    rcases le_total a b with hab | hba
    · rw [min_eq_left (by exact_mod_cast hab)]
    · rw [min_eq_right (by exact_mod_cast hba)]
  have hbase : min (a : ℝ) (b : ℝ) ≤ (c : ℝ) := by
    rw [hmin_real]
    exact_mod_cast h
  have hmin : -(c : ℝ) / (d place : ℝ) ≤
      -min (a : ℝ) (b : ℝ) / (d place : ℝ) :=
    div_le_div_of_nonneg_right (neg_le_neg hbase) hd.le
  have hcases : -(c : ℝ) / (d place : ℝ) ≤ -(a : ℝ) / (d place : ℝ) ∨
      -(c : ℝ) / (d place : ℝ) ≤ -(b : ℝ) / (d place : ℝ) := by
    rcases le_total a b with hab | hba
    · left
      have hmin' : min (a : ℝ) (b : ℝ) = (a : ℝ) := by
        exact_mod_cast min_eq_left hab
      simpa [hmin'] using hmin
    · right
      have hmin' : min (a : ℝ) (b : ℝ) = (b : ℝ) := by
        exact_mod_cast min_eq_right hba
      simpa [hmin'] using hmin
  rcases hcases with hca | hcb
  · calc (absNorm place) ^ (-(c : ℝ) / (d place : ℝ))
        ≤ (absNorm place) ^ (-(a : ℝ) / (d place : ℝ)) :=
          (Real.rpow_le_rpow_left_iff (absNorm_gt_one place)).mpr hca
      _ ≤ max ((absNorm place) ^ (-(a : ℝ) / (d place : ℝ)))
            ((absNorm place) ^ (-(b : ℝ) / (d place : ℝ))) := le_max_left _ _
  · calc (absNorm place) ^ (-(c : ℝ) / (d place : ℝ))
        ≤ (absNorm place) ^ (-(b : ℝ) / (d place : ℝ)) :=
          (Real.rpow_le_rpow_left_iff (absNorm_gt_one place)).mpr hcb
      _ ≤ max ((absNorm place) ^ (-(a : ℝ) / (d place : ℝ)))
            ((absNorm place) ^ (-(b : ℝ) / (d place : ℝ))) := le_max_right _ _

theorem canonicalAbsValueFun_add_le_max (x y : N place) :
    canonicalAbsValueFun place (x + y) ≤
      max (canonicalAbsValueFun place x) (canonicalAbsValueFun place y) := by
  by_cases hx : x = 0
  · subst hx
    simp [canonicalAbsValueFun]
  · by_cases hy : y = 0
    · subst hy
      simp [canonicalAbsValueFun]
    · by_cases hxy : x + y = 0
      · rw [hxy, canonicalAbsValueFun_zero]
        exact le_max_of_le_left (canonicalAbsValueFun_nonneg place x)
      · rw [canonicalAbsValueFun_of_ne place hxy,
          canonicalAbsValueFun_of_ne place hx,
          canonicalAbsValueFun_of_ne place hy]
        exact rpow_exponent_le_max place (nu place x) (nu place y) (nu place (x + y))
          (nu_add_ge_min_of_add_ne_zero place hx hy hxy)

theorem canonicalAbsValueFun_add_le (x y : N place) :
    canonicalAbsValueFun place (x + y) ≤
      canonicalAbsValueFun place x + canonicalAbsValueFun place y := by
  refine le_trans (canonicalAbsValueFun_add_le_max place x y) (max_le ?_ ?_)
  · linarith [canonicalAbsValueFun_nonneg place y]
  · linarith [canonicalAbsValueFun_nonneg place x]

noncomputable def canonicalAbsValue : AbsoluteValue (N place) ℝ where
  toFun := canonicalAbsValueFun place
  map_mul' := canonicalAbsValueFun_mul place
  nonneg' := canonicalAbsValueFun_nonneg place
  eq_zero' := canonicalAbsValueFun_eq_zero_iff place
  add_le' := canonicalAbsValueFun_add_le place

@[simp] theorem canonicalAbsValue_zero : canonicalAbsValue place 0 = 0 :=
  canonicalAbsValueFun_zero place

theorem canonicalAbsValue_of_ne {x : N place} (hx : x ≠ 0) :
    canonicalAbsValue place x =
      (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ)) :=
  canonicalAbsValueFun_of_ne place hx

def ScalarExtensionCompatibility : Prop :=
  ∀ q : K place,
    canonicalAbsValue place (algebraMap (K place) (N place) q) = ‖q‖

theorem spectralNorm_extends_scalars (q : K place) :
    spectralNorm (K place) (N place) (algebraMap (K place) (N place) q) = ‖q‖ :=
  spectralNorm_extends q

theorem canonicalAbsValue_eq_spectralNorm
    (h : ScalarExtensionCompatibility place) (x : N place) :
    canonicalAbsValue place x = spectralNorm (K place) (N place) x :=
  spectralNorm_unique_field_norm_ext (K := K place) (L := N place)
    (f := canonicalAbsValue place) (h) x

theorem normalizedNorm_eq_formula_of_scalarExtension
    (h : ScalarExtensionCompatibility place) (x : N place) :
    ‖x‖ = if x = 0 then 0 else
      (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ)) := by
  classical
  rw [show ‖x‖ = spectralNorm (K place) (N place) x from rfl]
  exact (canonicalAbsValue_eq_spectralNorm place h x).symm

theorem normalizedNorm_eq_formula_of_ne
    (h : ScalarExtensionCompatibility place) {x : N place} (hx : x ≠ 0) :
    ‖x‖ = (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ)) := by
  rw [normalizedNorm_eq_formula_of_scalarExtension place h x, if_neg hx]

theorem normalizedNorm_formula_at_zero
    (h : ScalarExtensionCompatibility place) :
    ‖(0 : N place)‖ = 0 := by
  classical
  rw [normalizedNorm_eq_formula_of_scalarExtension place h 0]
  simp

theorem normalizedCanonicalPowerComparison
    (h : ScalarExtensionCompatibility place) (x : N place) (hx : x ≠ 0) :
    ‖x‖ ^ d place = ((absNorm place) ^ nu place x)⁻¹ := by
  rw [normalizedNorm_eq_formula_of_ne place h hx]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (absNorm_pos place))]
  rw [show -(nu place x : ℝ) / (d place : ℝ) * (d place : ℕ) =
      -(nu place x : ℝ) from by
    field_simp [ne_of_gt (by exact_mod_cast d_pos place : (0 : ℝ) < (d place : ℝ))]]
  rw [Real.rpow_neg (le_of_lt (absNorm_pos place)), Real.rpow_intCast]

theorem normalizedNorm_eq_formula_prime_of_absNorm
    (h : ScalarExtensionCompatibility place)
    (habs : absNorm place = (pNat place : ℝ) ^ f place)
    {x : N place} (hx : x ≠ 0) :
    ‖x‖ = (pNat place : ℝ) ^ (-(nu place x : ℝ) / (e place : ℝ)) := by
  rw [normalizedNorm_eq_formula_of_ne place h hx, habs, d_eq_e_mul_f]
  rw [← Real.rpow_natCast (pNat place : ℝ) (f place)]
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (pNat place : ℝ))]
  congr 1
  have he : (0 : ℝ) < (e place : ℝ) := by exact_mod_cast e_pos place
  have hf : (0 : ℝ) < (f place : ℝ) := by exact_mod_cast f_pos place
  field_simp [ne_of_gt he, ne_of_gt hf]
  push_cast
  ring

end LeanFormal.IUT.XiFPaper.S1448ReportENormalizedNormActual

end
