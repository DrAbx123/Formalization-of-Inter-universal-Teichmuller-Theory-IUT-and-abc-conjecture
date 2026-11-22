import LeanFormal.IUT.Foundations.AlgebraicGeometry.BaseScalarValuationRelation
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

/-!
# General normalized norm formula via spectral uniqueness

Using the base-scalar valuation relation, define the canonical absolute value

  `f x = absNorm ^ (-(ν(x)/d))`,  `ν(x) = -log (Valued.v x)`,

on the completed field (with the convention `f 0 = 0`, forced by
`AbsoluteValue.eq_zero'`; note `ν(0) = 0` by the junk value of `log 0`).
It extends the p-adic norm on `PadicScalarField`.  Mathlib's
`spectralNorm_unique_field_norm_ext` then identifies `f` with the normalized
spectral norm.  This yields the general normalized norm formula, as a *power*
relation

  `‖x‖ = absNorm ^ (-(ν(x)/d))`

for nonzero `x` (it does not assert `‖x‖ = ‖x‖_def` unless `d = 1`), and
`normalizedCanonicalPowerComparison`.

The carrier `L` is the normalized completion (with the spectral norm), while
`C` is the canonical adic completion (with the valued-adic norm), used only for
`Valued.v` and `ν`; both are definitionally the same field.

No fake absolute value and no norm equality: completion and algebraic instance
obligations are discharged from finite dimensionality and production instances.
-/


set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

noncomputable section

namespace LeanFormal.IUT.GeneralNormalizedNormBySpectralUniqueness

open scoped WithZero Valued Topology NNReal
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.BaseScalarValuationRelation

universe u

variable {F : Type u} [Field F] [NumberField F] (place : NumberField.FinitePlace F)

abbrev K : Type := PadicScalarField place
abbrev C : Type u := place.maximalIdeal.adicCompletion F
abbrev L : Type u := LeanFormal.IUT.NumberFieldFinitePlace.NormalizedCompletion place
abbrev pNat : ℕ := (LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime place).val
abbrev e : ℕ := relativeRamificationIndex (k := ℚ) place
abbrev f : ℕ := relativeResidueDegree (k := ℚ) place
abbrev d : ℕ := relativeCompletionDegree (k := ℚ) place
abbrev absNorm : ℝ := (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ)

theorem absNorm_gt_one : 1 < absNorm place := by
  unfold absNorm
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm place.maximalIdeal

theorem absNorm_pos : (0 : ℝ) < absNorm place := lt_trans zero_lt_one (absNorm_gt_one place)

theorem d_eq_e_mul_f : d place = e place * f place := rfl

theorem absNorm_lower :
    Ideal.absNorm (comap (k := ℚ) place).maximalIdeal.asIdeal = pNat place := by
  let v := (comap (k := ℚ) place).maximalIdeal
  let ee : NumberField.RingOfIntegers ℚ ≃+* ℤ :=
    Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)
  have hgen : Rat.HeightOneSpectrum.natGenerator v = pNat place := rfl
  have hspan : Ideal.span {(pNat place : ℤ)} = v.asIdeal.map ee := by
    rw [← hgen]
    rw [← Rat.HeightOneSpectrum.span_natGenerator v]
  have hcard : Ideal.absNorm v.asIdeal = Ideal.absNorm (Ideal.span {(pNat place : ℤ)}) := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply]
    exact Nat.card_congr (Ideal.quotientEquiv v.asIdeal (Ideal.span {(pNat place : ℤ)})
      ee hspan).toEquiv
  rw [hcard]
  rw [Ideal.absNorm_span_natCast]
  simp

theorem absNorm_eq_pow_f :
    absNorm place = (pNat place : ℝ) ^ f place := by
  rw [absNorm]
  rw [absNorm_eq_pow_relativeResidueDegree (k := ℚ) place]
  rw [absNorm_lower place]

/-- The normalized carrier viewed as the canonical completion carrier. -/
noncomputable def toC (x : L place) : C place := x

theorem toC_apply (x : L place) : toC place x = x := rfl

theorem toC_add (x y : L place) : toC place (x + y) = toC place x + toC place y := rfl

theorem toC_mul (x y : L place) : toC place (x * y) = toC place x * toC place y := rfl

theorem toC_zero : toC place 0 = 0 := rfl

noncomputable def nu (x : L place) : ℤ :=
  -WithZero.log (Valued.v (toC place x))

theorem nu_add_ge_min (x y : L place) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (nu place x) (nu place y) ≤ nu place (x + y) := by
  have hvx : (Valued.v (toC place x) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    valuation_ne_zero_of_ne_zero place (toC place x) hx
  have hvy : (Valued.v (toC place y) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    valuation_ne_zero_of_ne_zero place (toC place y) hy
  have hvs : (Valued.v (toC place (x + y)) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    valuation_ne_zero_of_ne_zero place (toC place (x + y)) hxy
  have hmap : (Valued.v (toC place (x + y)) : WithZero (Multiplicative ℤ)) ≤
      max (Valued.v (toC place x)) (Valued.v (toC place y)) := by
    have h := (Valued.v : Valuation (C place) (WithZero (Multiplicative ℤ))).map_add
      (toC place x) (toC place y)
    rw [toC_add]
    exact h
  have hlog : WithZero.log (Valued.v (toC place (x + y))) ≤
      max (WithZero.log (Valued.v (toC place x)))
        (WithZero.log (Valued.v (toC place y))) := by
    by_cases hle : Valued.v (toC place x) ≤ Valued.v (toC place y)
    · have hmax : max (Valued.v (toC place x)) (Valued.v (toC place y)) =
          Valued.v (toC place y) := max_eq_right hle
      rw [hmax] at hmap
      exact ((WithZero.log_le_log hvs hvy).mpr hmap).trans (le_max_right _ _)
    · have hmax : max (Valued.v (toC place x)) (Valued.v (toC place y)) =
          Valued.v (toC place x) := max_eq_left (le_of_not_ge hle)
      rw [hmax] at hmap
      exact ((WithZero.log_le_log hvs hvx).mpr hmap).trans (le_max_left _ _)
  unfold nu
  rcases le_total (WithZero.log (Valued.v (toC place x)))
      (WithZero.log (Valued.v (toC place y))) with h | h
  · have hmax : max (WithZero.log (Valued.v (toC place x)))
        (WithZero.log (Valued.v (toC place y))) =
        WithZero.log (Valued.v (toC place y)) := max_eq_right h
    rw [hmax] at hlog
    have h1 : -(WithZero.log (Valued.v (toC place y))) ≤
        -(WithZero.log (Valued.v (toC place (x + y)))) := neg_le_neg hlog
    have hmin : min (-(WithZero.log (Valued.v (toC place x))))
        (-(WithZero.log (Valued.v (toC place y)))) =
        -(WithZero.log (Valued.v (toC place y))) := by
      rw [min_eq_right]
      exact neg_le_neg h
    rw [hmin]
    exact h1
  · have hmax : max (WithZero.log (Valued.v (toC place x)))
        (WithZero.log (Valued.v (toC place y))) =
        WithZero.log (Valued.v (toC place x)) := max_eq_left h
    rw [hmax] at hlog
    have h1 : -(WithZero.log (Valued.v (toC place x))) ≤
        -(WithZero.log (Valued.v (toC place (x + y)))) := neg_le_neg hlog
    have hmin : min (-(WithZero.log (Valued.v (toC place x))))
        (-(WithZero.log (Valued.v (toC place y)))) =
        -(WithZero.log (Valued.v (toC place x))) := by
      rw [min_eq_left]
      exact neg_le_neg h
    rw [hmin]
    exact h1

noncomputable def canonicalFun (x : L place) : ℝ := by
  classical
  exact if x = 0 then 0 else (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ))

theorem canonicalFun_zero : canonicalFun place 0 = 0 := by
  unfold canonicalFun
  exact if_pos rfl

theorem canonicalFun_of_ne (x : L place) (hx : x ≠ 0) :
    canonicalFun place x = (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ)) := by
  unfold canonicalFun
  exact if_neg hx

theorem canonicalFun_nonneg (x : L place) : 0 ≤ canonicalFun place x := by
  by_cases hx : x = 0
  · rw [hx, canonicalFun_zero]
  · rw [canonicalFun_of_ne place x hx]
    exact Real.rpow_nonneg (absNorm_pos place).le _

theorem canonicalFun_eq_zero_iff (x : L place) : canonicalFun place x = 0 ↔ x = 0 := by
  constructor
  · intro hzero
    by_contra hx
    rw [canonicalFun_of_ne place x hx] at hzero
    have hpos : 0 < (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ)) :=
      Real.rpow_pos_of_pos (absNorm_pos place) _
    linarith
  · intro hx; subst hx; exact canonicalFun_zero place

theorem canonicalFun_add_le (x y : L place) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    canonicalFun place (x + y) ≤ max (canonicalFun place x) (canonicalFun place y) := by
  rw [canonicalFun_of_ne place (x + y) hxy, canonicalFun_of_ne place x hx,
    canonicalFun_of_ne place y hy]
  have hnu := nu_add_ge_min place x y hx hy hxy
  have hd : (0 : ℝ) < (d place : ℝ) := by
    exact_mod_cast relativeCompletionDegree_pos (k := ℚ) place
  have hexp : -(nu place (x + y) : ℝ) / (d place : ℝ) ≤
      max (-(nu place x : ℝ) / (d place : ℝ)) (-(nu place y : ℝ) / (d place : ℝ)) := by
    rcases le_total (nu place x) (nu place y) with h | h
    · have h1 : nu place x ≤ nu place (x + y) := by
        rwa [min_eq_left h] at hnu
      have hcast : -(nu place (x + y) : ℝ) ≤ -(nu place x : ℝ) := by
        exact_mod_cast (neg_le_neg h1 : -nu place (x + y) ≤ -nu place x)
      exact (div_le_div_of_nonneg_right hcast hd.le).trans (le_max_left _ _)
    · have h1 : nu place y ≤ nu place (x + y) := by
        rwa [min_eq_right h] at hnu
      have hcast : -(nu place (x + y) : ℝ) ≤ -(nu place y : ℝ) := by
        exact_mod_cast (neg_le_neg h1 : -nu place (x + y) ≤ -nu place y)
      exact (div_le_div_of_nonneg_right hcast hd.le).trans (le_max_right _ _)
  have hbase : 1 < absNorm place := absNorm_gt_one place
  have h1 := Real.rpow_le_rpow_of_exponent_le hbase.le hexp
  have h2 : (absNorm place) ^ max (-(nu place x : ℝ) / (d place : ℝ))
        (-(nu place y : ℝ) / (d place : ℝ)) ≤
      max ((absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ)))
        ((absNorm place) ^ (-(nu place y : ℝ) / (d place : ℝ))) := by
    rcases le_total (-(nu place x : ℝ) / (d place : ℝ)) (-(nu place y : ℝ) / (d place : ℝ)) with h | h
    · have hc := Real.rpow_le_rpow_of_exponent_le hbase.le h
      rw [max_eq_right h, max_eq_right hc]
    · have hc := Real.rpow_le_rpow_of_exponent_le hbase.le h
      rw [max_eq_left h, max_eq_left hc]
  exact h1.trans h2

theorem canonicalFun_add_le_sum (x y : L place) :
    canonicalFun place (x + y) ≤ canonicalFun place x + canonicalFun place y := by
  by_cases hx : x = 0
  · rw [hx, zero_add, canonicalFun_zero]
    linarith [canonicalFun_nonneg place y]
  · by_cases hy : y = 0
    · rw [hy, add_zero, canonicalFun_zero]
      linarith [canonicalFun_nonneg place x]
    · by_cases hxy : x + y = 0
      · rw [hxy, canonicalFun_zero]
        linarith [canonicalFun_nonneg place x, canonicalFun_nonneg place y]
      · exact (canonicalFun_add_le place x y hx hy hxy).trans
          (max_le_add_of_nonneg (canonicalFun_nonneg place x) (canonicalFun_nonneg place y))

noncomputable def canonicalAbsValue : AbsoluteValue (L place) ℝ where
  toFun := canonicalFun place
  map_mul' x y := by
    by_cases hx : x = 0
    · subst hx; simp [canonicalFun_zero]
    · by_cases hy : y = 0
      · subst hy; simp [canonicalFun_zero]
      · have hxy : x * y ≠ 0 := mul_ne_zero hx hy
        rw [canonicalFun_of_ne place (x * y) hxy, canonicalFun_of_ne place x hx,
          canonicalFun_of_ne place y hy]
        have hvx : (Valued.v (toC place x) : WithZero (Multiplicative ℤ)) ≠ 0 :=
          valuation_ne_zero_of_ne_zero place (toC place x) hx
        have hvy : (Valued.v (toC place y) : WithZero (Multiplicative ℤ)) ≠ 0 :=
          valuation_ne_zero_of_ne_zero place (toC place y) hy
        have hnu : nu place (x * y) = nu place x + nu place y := by
          unfold nu
          rw [toC_mul, map_mul, WithZero.log_mul hvx hvy]
          ring
        rw [hnu]
        rw [show -(((nu place x + nu place y : ℤ)) : ℝ) / (d place : ℝ) =
            (-(nu place x : ℝ) / (d place : ℝ)) + (-(nu place y : ℝ) / (d place : ℝ)) by
          push_cast
          ring]
        rw [Real.rpow_add (absNorm_pos place)]
  nonneg' x := canonicalFun_nonneg place x
  eq_zero' x := canonicalFun_eq_zero_iff place x
  add_le' x y := canonicalFun_add_le_sum place x y

theorem canonicalAbsValue_extends (q : K place) :
    canonicalAbsValue place (algebraMap (K place) (L place) q) = ‖q‖ := by
  by_cases hq : q = 0
  · subst hq
    show canonicalFun place (algebraMap (K place) (L place) (0 : K place)) = ‖(0 : K place)‖
    simp [canonicalFun]
  · obtain ⟨m, u, hdec, hval⟩ := baseScalarValuationRelation place q hq
    have halg : toC place (algebraMap (K place) (L place) q) =
        algebraMap (scalarField place) (completionField place) q := rfl
    have hval' : (Valued.v (toC place (algebraMap (K place) (L place) q)) :
        WithZero (Multiplicative ℤ)) = WithZero.exp (-(m * (e place : ℤ))) := by
      rw [halg, hval]
    have halg_ne : algebraMap (K place) (L place) q ≠ 0 := by
      intro h0
      have hzero : (Valued.v (toC place (algebraMap (K place) (L place) q)) :
          WithZero (Multiplicative ℤ)) = 0 := by
        rw [h0]
        rw [toC_zero, map_zero]
      rw [hval'] at hzero
      exact WithZero.exp_ne_zero hzero
    have hqnorm : ‖q‖ = (pNat place : ℝ) ^ (-m : ℤ) := by
      rw [hdec]
      rw [norm_mul, norm_zpow, PadicInt.algebraMap_apply, scalarPrime_norm place,
        padicUnit_norm_one place u, mul_one]
      rw [inv_zpow]
      rw [zpow_neg]
    have hnu : nu place (algebraMap (K place) (L place) q) = m * (e place : ℤ) := by
      unfold nu
      rw [hval', WithZero.log_exp]
      ring
    have hfun : canonicalFun place (algebraMap (K place) (L place) q) =
        (absNorm place) ^ (-((m : ℝ) * (e place : ℝ)) / (d place : ℝ)) := by
      rw [canonicalFun_of_ne place _ halg_ne, hnu]
      congr 1
      push_cast
      ring
    have he0 : (e place : ℝ) ≠ 0 := by
      have h := relativeRamificationIndex_ne_zero (k := ℚ) place
      exact_mod_cast h
    have hf0 : (f place : ℝ) ≠ 0 := by
      have h := relativeResidueDegree_ne_zero (k := ℚ) place
      exact_mod_cast h
    have hexp : (f place : ℝ) * (-((m : ℝ) * (e place : ℝ)) / (d place : ℝ)) =
        -(m : ℝ) := by
      rw [d_eq_e_mul_f]
      push_cast
      field_simp
    have hp0 : (0 : ℝ) ≤ (pNat place : ℝ) := by
      have hprime : (pNat place).Prime :=
        (LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime place).2
      have hpos : (0 : ℝ) < (pNat place : ℝ) := by exact_mod_cast hprime.pos
      exact hpos.le
    show canonicalFun place (algebraMap (K place) (L place) q) = ‖q‖
    calc canonicalFun place (algebraMap (K place) (L place) q)
        = (absNorm place) ^ (-((m : ℝ) * (e place : ℝ)) / (d place : ℝ)) := hfun
      _ = ((pNat place : ℝ) ^ f place) ^
            (-((m : ℝ) * (e place : ℝ)) / (d place : ℝ)) := by rw [absNorm_eq_pow_f]
      _ = ((pNat place : ℝ) ^ (f place : ℝ)) ^
            (-((m : ℝ) * (e place : ℝ)) / (d place : ℝ)) := by rw [Real.rpow_natCast]
      _ = (pNat place : ℝ) ^
            ((f place : ℝ) * (-((m : ℝ) * (e place : ℝ)) / (d place : ℝ))) := by
            rw [← Real.rpow_mul hp0]
      _ = (pNat place : ℝ) ^ (-(m : ℝ)) := by rw [hexp]
      _ = (pNat place : ℝ) ^ ((-m : ℤ) : ℝ) := by
            congr 1
            push_cast
            ring
      _ = (pNat place : ℝ) ^ (-m : ℤ) := by rw [Real.rpow_intCast]
      _ = ‖q‖ := hqnorm.symm

theorem canonicalAbsValue_eq_spectralNorm (x : L place) :
    canonicalAbsValue place x = spectralNorm (K place) (L place) x :=
  spectralNorm_unique_field_norm_ext (K := K place) (L := L place)
    (f := canonicalAbsValue place) (canonicalAbsValue_extends place) x

theorem generalNormalizedNormFormula (x : L place) (hx : x ≠ 0) :
    ‖x‖ = (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ)) := by
  have hnorm : ‖x‖ = spectralNorm (K place) (L place) x := rfl
  rw [hnorm, ← canonicalAbsValue_eq_spectralNorm place x]
  exact canonicalFun_of_ne place x hx

theorem normalizedCanonicalPowerComparison (x : L place) (hx : x ≠ 0) :
    ‖x‖ ^ (d place) = ((absNorm place) ^ nu place x)⁻¹ := by
  rw [generalNormalizedNormFormula place x hx]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (absNorm_pos place).le]
  rw [show (-(nu place x : ℝ) / (d place : ℝ)) * (d place : ℕ) = -(nu place x : ℝ) by
    have hd : (d place : ℝ) ≠ 0 := by
      have h : (0 : ℝ) < (d place : ℝ) := by
        exact_mod_cast relativeCompletionDegree_pos (k := ℚ) place
      exact ne_of_gt h
    field_simp [hd]]
  rw [Real.rpow_neg (absNorm_pos place).le]
  rw [Real.rpow_intCast]

end LeanFormal.IUT.GeneralNormalizedNormBySpectralUniqueness

end