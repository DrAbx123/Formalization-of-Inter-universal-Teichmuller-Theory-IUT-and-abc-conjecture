import LeanFormal.IUT.Foundations.Geometry.TateCoordinateSeries
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Tactic

/-! # Local-field support for the pole-excluded q-parameter domain

For a complete nonarchimedean field K and a q-parameter q with 0 < ||q|| < 1,
the parameter u = 1 + q lies on the unit-sphere (an open-ball/norm fact) and is
pole-excluded: q^n (1+q) != 1 for every n in Z, because for n >= 0 the product
has norm < 1 while for n < 0 it has norm > 1.  Hence the pole-excluded
parameter domain is nonempty, the basic local-field input for the q-parameter
point map.  Scratch only; no production edits. -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open LeanFormal.IUT.TateCurve

namespace LeanFormal.IUT.TatePointLocal

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The parameter 1 + q is a unit: its norm is one. -/
theorem norm_one_add_eq_one {q : K} (hq : ‖q‖ < 1) : ‖(1 : K) + q‖ = 1 := by
  have hne : ‖(1 : K)‖ ≠ ‖q‖ := by
    simpa using ne_of_gt hq
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one,
    max_eq_left hq.le]

/-- The parameter 1 + q is nonzero. -/
theorem one_add_ne_zero {q : K} (hq : ‖q‖ < 1) : (1 : K) + q ≠ 0 := by
  intro h
  have hqeq : q = -1 := by linear_combination h
  rw [hqeq, norm_neg, norm_one] at hq
  exact lt_irrefl 1 hq

/-- Positive powers of q have norm below one. -/
theorem norm_pow_lt_one {q : K} (hq : ‖q‖ < 1) {n : Nat} (hn : 0 < n) :
    ‖q ^ n‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg q) hq hn.ne'

/-- Negative powers of q have norm above one. -/
theorem one_lt_norm_zpow_neg {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {n : Nat} (hn : 0 < n) :
    1 < ‖q ^ (-(n : Int))‖ := by
  rw [zpow_neg, norm_inv, zpow_natCast, norm_pow]
  have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  exact (one_lt_inv₀ (pow_pos hqpos n)).mpr (pow_lt_one₀ (norm_nonneg q) hq hn.ne')

/-- The pole q^n (1+q) = 1 cannot occur for n >= 0. -/
theorem pole_excluded_nat {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (n : Nat) :
    q ^ (n : Int) * (1 + q) ≠ 1 := by
  intro h
  rw [zpow_natCast] at h
  by_cases hn : n = 0
  · subst hn
    have h1 : (1 : K) + q = 1 := by simpa using h
    exact hq0 (by linear_combination h1)
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnorm : ‖q ^ n * (1 + q)‖ < 1 := by
      rw [norm_mul, norm_one_add_eq_one hq, mul_one]
      exact norm_pow_lt_one hq hpos
    rw [h] at hnorm
    norm_num at hnorm

/-- The pole q^n (1+q) = 1 cannot occur for n < 0. -/
theorem pole_excluded_neg {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) {n : Nat} (hn : 0 < n) :
    q ^ (-(n : Int)) * (1 + q) ≠ 1 := by
  intro h
  have hnorm : 1 < ‖q ^ (-(n : Int)) * (1 + q)‖ := by
    rw [norm_mul, norm_one_add_eq_one hq, mul_one]
    exact one_lt_norm_zpow_neg hq0 hq hn
  rw [h, norm_one] at hnorm
  exact lt_irrefl 1 hnorm

/-- Every pole q^n (1+q) = 1 is excluded. -/
theorem coordinatePoleExclusion_one_add {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    coordinatePoleExclusion q (1 + q) := by
  intro n
  rcases Int.eq_nat_or_neg n with ⟨m, hm | hm⟩
  · subst hm
    exact pole_excluded_nat hq0 hq m
  · subst hm
    by_cases hm0 : m = 0
    · subst hm0
      simpa using pole_excluded_nat hq0 hq 0
    · exact pole_excluded_neg hq0 hq (Nat.pos_of_ne_zero hm0)

/-- The pole-excluded parameter domain is nonempty for any q-parameter
0 < ||q|| < 1: the unit-sphere parameter 1 + q belongs to it. -/
theorem coordinateParameterDomain_nonempty {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    (coordinateParameterDomain q).Nonempty :=
  ⟨1 + q, ⟨one_add_ne_zero hq, coordinatePoleExclusion_one_add hq0 hq⟩⟩

end LeanFormal.IUT.TatePointLocal
