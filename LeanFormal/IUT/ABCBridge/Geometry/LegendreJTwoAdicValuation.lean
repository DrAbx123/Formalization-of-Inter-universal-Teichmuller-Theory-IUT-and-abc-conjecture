import LeanFormal.IUT.ABCBridge.Geometry.LegendreWeierstrassCurve
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-!
# The valuation of the Legendre `j`-invariant

Port note: the six statements of this file are ported from the LANA Project
development (released under the Apache 2.0 license, `Authors: LANA Project`),
file `Iut/Tripod/TwoAdic.lean` lines 194-338: `valuation_legendre_ne_zero`,
`log_valuation_legendre_j`, `log_valuation_sq_sub_add_one_le`,
`log_valuation_legendre_j_le`, `one_lt_valuation_legendre_j` and
`ne_one_or_ne_one_of_one_lt_valuation_legendre_j`. The curve is this
repository's `legendreWeierstrassCurve` (`y^2 = x(x-1)(x-l)`, the same Legendre
family as the source `legendre`), whose `j`-invariant is
`legendreWeierstrassCurve_j`:
`256 * (l^2 - l + 1)^3 / (l^2 * (1 - l)^2)` (the source writes `(l - 1)^2` for
the last factor, an equal square in any field). The proofs are written
independently against the current Mathlib API.

Consumer: the Frey `j`-denominator `2`-adic valuation accounting of the
`ABCFreyJDenominatorHeightCriterion` route
(`ABCBridge/Bridge/ABCEllipticHeightCriterion.lean:40`): the identity
`log_valuation_legendre_j` is the factorized `ord_w(j)`, the inequality
`log_valuation_legendre_j_le` is the placewise bound
`ord_w(j) <= 2*|ord_w(l)| + 2*|ord_w(l - 1)|` used for the `2`-adic
contribution, and the two `one_lt` statements detect the places where `l`
meets `{0, 1}`.
-/

namespace LeanFormal.IUT

open WithZero

open scoped WithZero

/-- Ultrametric inequality for `l^2 - l + 1 = l * (l - 1) + 1`. Port of
`log_valuation_sq_sub_add_one_le` (`Iut/Tripod/TwoAdic.lean:219`). -/
lemma log_valuation_sq_sub_add_one_le {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰) {l : K}
    (hc : v (l ^ 2 - l + 1) ≠ 0) (hl : v l ≠ 0) (hl1 : v (l - 1) ≠ 0) :
    log (v (l ^ 2 - l + 1)) ≤ log (v l) + log (v (l - 1)) ∨
      log (v (l ^ 2 - l + 1)) ≤ 0 := by
  have hfactor : l ^ 2 - l + 1 = l * (l - 1) + 1 := by ring
  rw [hfactor] at hc ⊢
  rcases Valuation.map_add' v (l * (l - 1)) 1 with hle | hle
  · left
    have hle' : v (l * (l - 1) + 1) ≤ v l * v (l - 1) := by
      simpa only [map_mul] using hle
    calc log (v (l * (l - 1) + 1)) ≤ log (v l * v (l - 1)) :=
          (log_le_log hc (mul_ne_zero hl hl1)).mpr hle'
      _ = log (v l) + log (v (l - 1)) := log_mul hl hl1
  · right
    have hle' : v (l * (l - 1) + 1) ≤ 1 := by simpa using hle
    calc log (v (l * (l - 1) + 1)) ≤ log 1 := (log_le_log hc one_ne_zero).mpr hle'
      _ = 0 := log_one

variable {K : Type*} [Field K] [NeZero (2 : K)] (v : Valuation K ℤᵐ⁰) {l : K}
  [(legendreWeierstrassCurve l).IsElliptic]

/-- The nonvanishing of the factors of `j`, from `v(j) ≠ 0`. Port of
`valuation_legendre_ne_zero` (`Iut/Tripod/TwoAdic.lean:194`). -/
lemma valuation_legendre_ne_zero (hj : v (legendreWeierstrassCurve l).j ≠ 0) :
    v 256 ≠ 0 ∧ v (l ^ 2 - l + 1) ≠ 0 ∧ v l ≠ 0 ∧ v (l - 1) ≠ 0 := by
  have hparam : l ≠ 0 ∧ l ≠ 1 :=
    (legendreWeierstrassCurve_isElliptic_iff l (NeZero.ne (2 : K))).mp
      (inferInstance : (legendreWeierstrassCurve l).IsElliptic)
  rw [legendreWeierstrassCurve_j, map_div₀, map_mul, map_mul, map_pow, map_pow,
    map_pow] at hj
  have hnum : v 256 * v (l ^ 2 - l + 1) ^ 3 ≠ 0 := (div_ne_zero_iff.mp hj).1
  have hQ : v (l ^ 2 - l + 1) ≠ 0 :=
    (pow_ne_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp (mul_ne_zero_iff.mp hnum).2
  exact ⟨(mul_ne_zero_iff.mp hnum).1, hQ,
    (Valuation.ne_zero_iff v).mpr hparam.1,
    (Valuation.ne_zero_iff v).mpr (sub_ne_zero.mpr hparam.2)⟩

/-- The factorized valuation of `j`. Port of `log_valuation_legendre_j`
(`Iut/Tripod/TwoAdic.lean:205`). -/
lemma log_valuation_legendre_j (hj : v (legendreWeierstrassCurve l).j ≠ 0) :
    log (v (legendreWeierstrassCurve l).j) =
      log (v 256) + 3 * log (v (l ^ 2 - l + 1)) -
        (2 * log (v l) + 2 * log (v (l - 1))) := by
  obtain ⟨h256, hQ, hl, hl1⟩ := valuation_legendre_ne_zero v hj
  have hswap : v (1 - l) = v (l - 1) := (Valuation.map_sub_swap v l 1).symm
  have hl1' : v (1 - l) ≠ 0 := by
    rw [hswap]
    exact hl1
  have hvd : v (legendreWeierstrassCurve l).j =
      v 256 * v (l ^ 2 - l + 1) ^ 3 / (v l ^ 2 * v (1 - l) ^ 2) := by
    rw [legendreWeierstrassCurve_j, map_div₀, map_mul, map_mul, map_pow, map_pow,
      map_pow]
  rw [hvd, log_div (mul_ne_zero h256 (pow_ne_zero 3 hQ))
      (mul_ne_zero (pow_ne_zero 2 hl) (pow_ne_zero 2 hl1')),
    log_mul h256 (pow_ne_zero 3 hQ), log_pow,
    log_mul (pow_ne_zero 2 hl) (pow_ne_zero 2 hl1'), log_pow, log_pow, hswap]
  simp only [nsmul_eq_mul]
  ring

/-- The placewise bound on `log v(j)`: if `v(256) ≤ 1` then
`log v(j) ≤ 2*|log v(l)| + 2*|log v(l - 1)|`. Port of
`log_valuation_legendre_j_le` (`Iut/Tripod/TwoAdic.lean:237`). -/
lemma log_valuation_legendre_j_le (h256 : v 256 ≤ 1)
    (hj : v (legendreWeierstrassCurve l).j ≠ 0) :
    log (v (legendreWeierstrassCurve l).j) ≤
      2 * |log (v l)| + 2 * |log (v (l - 1))| := by
  obtain ⟨h256', hQ, hl, hl1⟩ := valuation_legendre_ne_zero v hj
  have hlog256 : log (v 256) ≤ 0 := by
    have := (log_le_log h256' one_ne_zero).mpr h256
    simpa using this
  rcases log_valuation_sq_sub_add_one_le v hQ hl hl1 with hsq | hsq
  · have h1 : log (v (legendreWeierstrassCurve l).j) ≤
        log (v l) + log (v (l - 1)) := by
      rw [log_valuation_legendre_j v hj]
      linarith
    calc log (v (legendreWeierstrassCurve l).j) ≤ log (v l) + log (v (l - 1)) := h1
      _ ≤ |log (v l)| + |log (v (l - 1))| := by
          linarith [le_abs_self (log (v l)), le_abs_self (log (v (l - 1)))]
      _ ≤ 2 * |log (v l)| + 2 * |log (v (l - 1))| := by
          linarith [abs_nonneg (log (v l)), abs_nonneg (log (v (l - 1)))]
  · have h1 : log (v (legendreWeierstrassCurve l).j) ≤
        -(2 * log (v l) + 2 * log (v (l - 1))) := by
      rw [log_valuation_legendre_j v hj]
      linarith
    calc log (v (legendreWeierstrassCurve l).j) ≤
          -(2 * log (v l) + 2 * log (v (l - 1))) := h1
      _ = -2 * log (v l) - 2 * log (v (l - 1)) := by ring
      _ ≤ 2 * |log (v l)| + 2 * |log (v (l - 1))| := by
          linarith [neg_abs_le (log (v l)), neg_abs_le (log (v (l - 1)))]

/-- **`v(j(E_λ)) > 1` at a place where `λ` meets `{0, 1, ∞}`**, for `v(2) = 1`: if
`v(λ) ≠ 1` or `v(λ − 1) ≠ 1` then `v(j) > 1`. Port of `one_lt_valuation_legendre_j`
(`Iut/Tripod/TwoAdic.lean:258`). Consumer: the place detection feeding the
`2`-adic Frey `j`-denominator accounting recorded in the module docstring. -/
lemma one_lt_valuation_legendre_j (h2 : v 2 = 1) (h : v l ≠ 1 ∨ v (l - 1) ≠ 1) :
    1 < v (legendreWeierstrassCurve l).j := by
  have h256 : v 256 = 1 := by
    have : (256 : K) = 2 ^ 8 := by norm_num
    rw [this, map_pow, h2, one_pow]
  have hparam : l ≠ 0 ∧ l ≠ 1 :=
    (legendreWeierstrassCurve_isElliptic_iff l (NeZero.ne (2 : K))).mp
      (inferInstance : (legendreWeierstrassCurve l).IsElliptic)
  have hvl : v l ≠ 0 := (Valuation.ne_zero_iff v).mpr hparam.1
  have hvl1 : v (l - 1) ≠ 0 :=
    (Valuation.ne_zero_iff v).mpr (sub_ne_zero.mpr hparam.2)
  have hfactor : ∃ c : ℤᵐ⁰, v (l ^ 2 - l + 1) = c ∧ c ≠ 0 ∧
      0 < 3 * log c - (2 * log (v l) + 2 * log (v (l - 1))) := by
    rcases lt_trichotomy (v l) 1 with hlt | heq | hgt
    · have hb : v (l - 1) = 1 := by
        rw [Valuation.map_sub_eq_of_lt_right v (by rw [map_one]; exact hlt), map_one]
      have hc : v (l ^ 2 - l + 1) = 1 := by
        have hlt' : v (l ^ 2 - l) < v 1 := by
          rw [map_one]
          refine lt_of_le_of_lt (Valuation.map_sub v _ _) (max_lt ?_ hlt)
          rw [map_pow]
          exact pow_lt_one₀ zero_le hlt (by norm_num)
        rw [Valuation.map_add_eq_of_lt_right v hlt', map_one]
      refine ⟨1, hc, one_ne_zero, ?_⟩
      have : log (v l) < 0 := by
        rw [← log_one]
        exact (log_lt_log hvl one_ne_zero).mpr hlt
      rw [hb]
      simp only [log_one]
      linarith
    · have hb : v (l - 1) ≠ 1 := h.resolve_left (not_not.mpr heq)
      have hb' : v (l - 1) < 1 := by
        refine lt_of_le_of_ne ?_ hb
        have := Valuation.map_sub v l 1
        rwa [heq, map_one, max_self] at this
      have hc : v (l ^ 2 - l + 1) = 1 := by
        have e : l ^ 2 - l + 1 = l * (l - 1) + 1 := by ring
        have hlt' : v (l * (l - 1)) < v 1 := by
          rw [map_mul, heq, one_mul, map_one]
          exact hb'
        rw [e, Valuation.map_add_eq_of_lt_right v hlt', map_one]
      refine ⟨1, hc, one_ne_zero, ?_⟩
      have : log (v (l - 1)) < 0 := by
        rw [← log_one]
        exact (log_lt_log hvl1 one_ne_zero).mpr hb'
      rw [heq]
      simp only [log_one]
      linarith
    · have hb : v (l - 1) = v l :=
        Valuation.map_sub_eq_of_lt_left v (by rw [map_one]; exact hgt)
      have hc : v (l ^ 2 - l + 1) = v l ^ 2 := by
        have e : l ^ 2 - l + 1 = l ^ 2 + (1 - l) := by ring
        have hlt' : v (1 - l) < v (l ^ 2) := by
          rw [Valuation.map_sub_swap, hb, map_pow]
          exact lt_self_pow₀ hgt (by norm_num)
        rw [e, Valuation.map_add_eq_of_lt_left v hlt', map_pow]
      refine ⟨v l ^ 2, hc, pow_ne_zero _ hvl, ?_⟩
      have : 0 < log (v l) := by
        rw [← log_one]
        exact (log_lt_log one_ne_zero hvl).mpr hgt
      rw [hb, log_pow]
      simp only [nsmul_eq_mul]
      push_cast
      linarith
  obtain ⟨c, hc, hc0, hpos⟩ := hfactor
  have hj : v (legendreWeierstrassCurve l).j ≠ 0 := by
    have hswap : v (1 - l) = v (l - 1) := (Valuation.map_sub_swap v l 1).symm
    have hvl1' : v (1 - l) ≠ 0 := by
      rw [hswap]
      exact hvl1
    rw [legendreWeierstrassCurve_j, map_div₀, map_mul, map_pow, hc, h256, map_mul,
      map_pow, map_pow]
    exact div_ne_zero (mul_ne_zero one_ne_zero (pow_ne_zero _ hc0))
      (mul_ne_zero (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1'))
  rw [← exp_log hj, ← exp_zero, exp_lt_exp, log_valuation_legendre_j v hj, h256,
    log_one, hc]
  linarith

/-- The converse: `v(j) > 1` forces `v(λ) ≠ 1` or `v(λ − 1) ≠ 1`, for `v(256) ≤ 1`.
Port of `ne_one_or_ne_one_of_one_lt_valuation_legendre_j`
(`Iut/Tripod/TwoAdic.lean:329`). -/
lemma ne_one_or_ne_one_of_one_lt_valuation_legendre_j (h256 : v 256 ≤ 1)
    (h : 1 < v (legendreWeierstrassCurve l).j) : v l ≠ 1 ∨ v (l - 1) ≠ 1 := by
  by_contra hcon
  have hvl_one : v l = 1 := not_not.mp (not_or.mp hcon).1
  have hsub_one : v (l - 1) = 1 := not_not.mp (not_or.mp hcon).2
  have hj : v (legendreWeierstrassCurve l).j ≠ 0 := ne_of_gt (zero_lt_one.trans h)
  have hle := log_valuation_legendre_j_le v h256 hj
  rw [hvl_one, hsub_one] at hle
  simp only [log_one, abs_zero, mul_zero, add_zero] at hle
  rw [← exp_log hj, ← exp_zero, exp_lt_exp] at h
  exact absurd h (not_lt_of_ge hle)

end LeanFormal.IUT
