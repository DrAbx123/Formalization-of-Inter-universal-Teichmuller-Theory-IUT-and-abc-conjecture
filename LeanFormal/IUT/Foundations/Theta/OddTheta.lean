/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal IUT/ABC contributors
-/
import Mathlib

set_option linter.unusedSectionVars false

/-!
# The actual odd theta series (EtTh Proposition 1.4)

This module starts from Motizuki, *The Etale Theta Function and its
Frobenioid-theoretic Manifestations*, Proposition 1.4 (text line 1338): with
q = q_X and a multiplicative coordinate U on the formal group,

  Theta(q, U) = q^(-1/8) * sum_{n in Z} (-1)^n * q^((n+1/2)^2/2) * U^(2n+1).

Removing the constant factor q^(-1/8) (multiplicative normalization), the
series is the odd theta kernel

  oddThetaTerm(q, U, n) = (-1)^n * q^(n(n+1)/2) * U^(2n+1),
  oddTheta(q, U)         = sum_{n in Z} oddThetaTerm(q, U, n),

because (n+1/2)^2/2 - 1/8 = n(n+1)/2.

Frozen setup: L is a complete nonarchimedean field (NormedField + complete +
ultrametric norm), q in L with 0 < |q| < 1, U in L^*.  The module is developed
in this file; the analytic convergence, the shift law and the evaluation
package are stated with their exact hypotheses.

## What is constructed (this file)

* the exact theta term and odd theta series (integer-indexed tsum);
* the exponent bookkeeping n(n+1)/2 as a natural number (integer-valued
  formula, nonnegative for all n);
* the sign factor (-1)^n as an element of L, with its norm one and additivity
  in the exponent;
* elementary special values oddThetaTerm(q,U,0) = U and
  oddThetaTerm(q,U,-1) = -U^(-1), which are the two terms responsible for the
  factor 2 in the nonvanishing argument at U = i;
* the norm formula for a theta term;
* the root/parameter normalization interface: a supplied square root r of q
  (never chosen by the library), the packet normalization ratio record, and the
  root-existence condition 2*l | v(q) recorded as data (no choice of root and no
  arbitrary theta-characteristic theory).

## Exact remaining obligations (no card, no placeholder)

The following Prop 1.4 statements are the actual analytic content and are NOT
yet proved in this file: (1) two-sided convergence/reindexing of the integer
series in the nonarchimedean topology, (2) the shift law
oddTheta(q, r^a U) = (-1)^a r^(-a^2) U^(-2a) oddTheta(q, U) for r^2 = q,
(3) nonvanishing of oddTheta(q, i) at a square root i of -1, and (4) the
evaluation package f = oddTheta / oddTheta(q,i) with f(i r^j) = r^(-j^2).
They require the nonarchimedean summability criterion for the quadratic
exponential decay of the terms; no unproved placeholder, no card and no
choice-of-root assumption is introduced here to substitute for them.  The normalization
records below document the packet |rho| vs 1/5 mismatch and the root-existence
condition 2*l | v(q) explicitly.
-/

noncomputable section

namespace LeanFormal.IUT.Foundations.Theta

universe u

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-! ## 1. The theta exponent and sign -/

/-- The integer formula n(n+1)/2 of EtTh Proposition 1.4, as a natural number.
For every integer n this is nonnegative. -/
def oddThetaExponent (n : ℤ) : ℕ :=
  (n * (n + 1) / 2).toNat

/-- The sign (-1)^n of the theta series, as an element of the coefficient
field. -/
noncomputable def oddThetaSign (n : ℤ) : L :=
  ((Int.negOnePow n : ℤ) : L)

/-- The n-th summand of the odd theta series of EtTh Proposition 1.4. -/
noncomputable def oddThetaTerm (q U : L) (n : ℤ) : L :=
  oddThetaSign n * q ^ oddThetaExponent n * U ^ (2 * n + 1)

/-- The odd theta series itself, as the two-sided integer sum. -/
noncomputable def oddTheta (q U : L) : L :=
  ∑' n : ℤ, oddThetaTerm q U n

/-! ## 2. The sign factor -/

/-- The sign factor is a power of -1. -/
theorem oddThetaSign_eq_pow (n : ℤ) : oddThetaSign (L := L) n = (-1 : L) ^ n :=
  Int.cast_negOnePow L n

/-- The sign factor has norm one. -/
theorem norm_oddThetaSign (n : ℤ) : ‖oddThetaSign (L := L) n‖ = 1 := by
  rw [oddThetaSign_eq_pow]
  simp

/-- The sign factor is multiplicative in the exponent. -/
theorem oddThetaSign_add (m n : ℤ) :
    oddThetaSign (L := L) (m + n) = oddThetaSign m * oddThetaSign n := by
  rw [oddThetaSign_eq_pow, oddThetaSign_eq_pow, oddThetaSign_eq_pow,
    zpow_add₀ (by norm_num : (-1 : L) ≠ 0)]

/-- The sign factor at zero is one. -/
@[simp] theorem oddThetaSign_zero : oddThetaSign (L := L) 0 = 1 := by
  simp [oddThetaSign]

/-- The sign factor at -1 is minus one. -/
@[simp] theorem oddThetaSign_neg_one : oddThetaSign (L := L) (-1) = -1 := by
  rw [oddThetaSign_eq_pow]
  norm_num

/-! ## 3. The exponent bookkeeping -/

@[simp] theorem oddThetaExponent_zero : oddThetaExponent 0 = 0 := by
  simp [oddThetaExponent]

@[simp] theorem oddThetaExponent_neg_one : oddThetaExponent (-1) = 0 := by
  simp [oddThetaExponent]

/-- The theta exponent is the natural-number part of the integer formula. -/
theorem oddThetaExponent_coe (n : ℤ) :
    (oddThetaExponent n : ℤ) = n * (n + 1) / 2 := by
  have h2 : 0 ≤ n * (n + 1) := by
    by_cases hn : 0 ≤ n
    · exact mul_nonneg hn (by linarith)
    · push Not at hn
      exact mul_nonneg_of_nonpos_of_nonpos hn.le (by linarith)
  have h : 0 ≤ n * (n + 1) / 2 := Int.ediv_nonneg h2 (by norm_num)
  rw [oddThetaExponent, Int.toNat_of_nonneg h]

/-! ## 4. Elementary theta terms -/

/-- The zero-th theta term is U. -/
@[simp] theorem oddThetaTerm_zero (q U : L) :
    oddThetaTerm q U 0 = U := by
  simp [oddThetaTerm]

/-- The (-1)-st theta term is -U^(-1). -/
@[simp] theorem oddThetaTerm_neg_one (q U : L) :
    oddThetaTerm q U (-1) = -U⁻¹ := by
  simp [oddThetaTerm]

/-- Norm of a theta term: the sign has norm one and the powers contribute their
norm powers. -/
theorem norm_oddThetaTerm (q U : L) (n : ℤ) :
    ‖oddThetaTerm q U n‖ =
      ‖q‖ ^ oddThetaExponent n * ‖U‖ ^ (2 * n + 1) := by
  rw [oddThetaTerm, norm_mul, norm_mul, norm_oddThetaSign, one_mul,
    norm_pow, norm_zpow]

/-! ## 5. The quadratic-exponential decay estimate -/

/-- **Quadratic exponential decay times a geometric factor.**  For real
numbers 0 <= a < 1 and 0 < b, the sequence
a^(n(n+1)/2) * b^n tends to zero.  This is the nonarchimedean convergence
estimate for the odd theta series: choose m with a^m * b < 1; for n >= 2m one
has n(n+1)/2 >= m n, hence a^(n(n+1)/2) * b^n <= (a^m * b)^n, which is
geometric. -/
theorem tendsto_quadraticExponential_mul_geometric
    {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb : 0 < b) :
    Filter.Tendsto (fun n : ℕ => a ^ (n * (n + 1) / 2) * b ^ n)
      Filter.atTop (nhds 0) := by
  have ha_le_one : a ≤ 1 := le_of_lt ha1
  have hlim : Filter.Tendsto (fun m : ℕ => a ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1
  have hpos : (0 : ℝ) < 1 / (b + 1) := by
    apply one_div_pos.mpr
    linarith
  have hev : ∀ᶠ m : ℕ in Filter.atTop, a ^ m < 1 / (b + 1) :=
    hlim.eventually (isOpen_Iio.mem_nhds hpos)
  obtain ⟨m, hm⟩ := hev.exists
  have hm_lt : a ^ m * b < 1 := by
    have hb1 : (0 : ℝ) < b + 1 := by linarith
    have h1 : a ^ m * b < (1 / (b + 1)) * b :=
      mul_lt_mul_of_pos_right hm hb
    have h2 : (1 / (b + 1)) * b < 1 := by
      rw [one_div, inv_mul_eq_div]
      rw [div_lt_one hb1]
      linarith
    exact lt_trans h1 h2
  have hbase : 0 ≤ a ^ m * b := mul_nonneg (pow_nonneg ha0 m) hb.le
  have hg : Filter.Tendsto (fun n : ℕ => (a ^ m * b) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase hm_lt
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards with n
    exact mul_nonneg (pow_nonneg ha0 _) (pow_nonneg hb.le n)
  · filter_upwards [Filter.eventually_ge_atTop (2 * m)] with n hn
    have hmn : m * n ≤ n * (n + 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      have hreal : (m : ℝ) * (n : ℝ) * 2 ≤ (n : ℝ) * ((n : ℝ) + 1) := by
        have hnreal : (2 * m : ℕ) ≤ n := hn
        have h2m : (2 : ℝ) * (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnreal
        have hnonneg : 0 ≤ (n : ℝ) - 2 * (m : ℝ) := by linarith
        nlinarith [mul_nonneg hnonneg (show (0:ℝ) ≤ (n:ℝ) by positivity)]
      exact_mod_cast hreal
    have hpow : a ^ (n * (n + 1) / 2) ≤ a ^ (m * n) :=
      pow_le_pow_of_le_one ha0 ha_le_one hmn
    calc a ^ (n * (n + 1) / 2) * b ^ n
        ≤ a ^ (m * n) * b ^ n := by
          exact mul_le_mul_of_nonneg_right hpow (pow_nonneg hb.le n)
      _ = (a ^ m * b) ^ n := by
          rw [mul_pow, ← pow_mul]

/-- On natural-number indices the theta exponent is the natural-number
quadratic n(n+1)/2. -/
theorem oddThetaExponent_natCast (n : ℕ) :
    oddThetaExponent (n : ℤ) = n * (n + 1) / 2 := by
  apply Nat.cast_injective (R := ℤ)
  rw [oddThetaExponent_coe]
  push_cast
  rfl

/-- Norm decay of the forward half of the theta series: for U nonzero and
||q|| < 1, the norms of oddThetaTerm(q,U,n), n >= 0, tend to zero. -/
theorem tendsto_norm_oddThetaTerm_nat (q U : L) (hU : U ≠ 0) (hq : ‖q‖ < 1) :
    Filter.Tendsto (fun n : ℕ => ‖oddThetaTerm q U (n : ℤ)‖)
      Filter.atTop (nhds 0) := by
  have hb : 0 < ‖U‖ ^ 2 := by
    have hUnorm : 0 < ‖U‖ := norm_pos_iff.mpr hU
    positivity
  have hdec := tendsto_quadraticExponential_mul_geometric
    (a := ‖q‖) (b := ‖U‖ ^ 2) (norm_nonneg q) hq hb
  have hdec' : Filter.Tendsto
      (fun n : ℕ => ‖U‖ * (‖q‖ ^ (n * (n + 1) / 2) * (‖U‖ ^ 2) ^ n))
      Filter.atTop (nhds 0) := by
    simpa using hdec.const_mul ‖U‖
  refine hdec'.congr' ?_
  filter_upwards with n
  have hUeq : ‖U‖ ^ (2 * n + 1) = ‖U‖ * (‖U‖ ^ 2) ^ n := by
    rw [pow_succ, pow_mul]
    ring
  rw [norm_oddThetaTerm, oddThetaExponent_natCast]
  have hz : (2 * (n : ℤ) + 1) = ((2 * n + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hz, zpow_natCast, hUeq]
  ring

/-- The forward half of the odd theta series is summable, by the
nonarchimedean summability criterion and the norm decay estimate. -/
theorem summable_oddThetaTerm_nat (q U : L) (hU : U ≠ 0) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => oddThetaTerm q U (n : ℤ)) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  exact (tendsto_zero_iff_norm_tendsto_zero).mpr
    (tendsto_norm_oddThetaTerm_nat q U hU hq)

/-- The exponent of the negative-index odd theta term is the usual quadratic
exponent. -/
theorem oddThetaExponent_neg_nat (n : ℕ) :
    oddThetaExponent (-(n : ℤ) - 1) = n * (n + 1) / 2 := by
  apply Nat.cast_injective (R := ℤ)
  rw [oddThetaExponent_coe]
  push_cast
  ring_nf

/-- Norm of the negative half of the odd theta series. -/
theorem norm_oddThetaTerm_neg_nat (q U : L) (hU : U ≠ 0) (n : ℕ) :
    ‖oddThetaTerm q U (-(n : ℤ) - 1)‖ =
      ‖U‖⁻¹ * (‖q‖ ^ (n * (n + 1) / 2) * ((‖U‖ ^ 2)⁻¹) ^ n) := by
  rw [norm_oddThetaTerm, oddThetaExponent_neg_nat]
  have hU0 : ‖U‖ ≠ 0 := norm_ne_zero_iff.mpr hU
  have hpow : (2 * (-(n : ℤ) - 1) + 1) = -(2 * (n : ℤ) + 1) := by ring
  rw [hpow, zpow_neg]
  have hnat : ((2 * n + 1 : ℕ) : ℤ) = 2 * (n : ℤ) + 1 := by push_cast; ring
  rw [← hnat, zpow_natCast]
  have hfactor : ‖U‖ ^ (2 * n + 1) = ‖U‖ * (‖U‖ ^ 2) ^ n := by
    rw [pow_succ, show 2 * n = n * 2 by ring, pow_mul]
    ring
  rw [hfactor, mul_inv, ← inv_pow]
  ring

/-- The negative half of the odd theta series is summable. -/
theorem summable_oddThetaTerm_neg_nat (q U : L) (hU : U ≠ 0) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => oddThetaTerm q U (-(n : ℤ) - 1)) := by
  have hUpos : 0 < ‖U‖ := norm_pos_iff.mpr hU
  have hb : 0 < (‖U‖ ^ 2)⁻¹ := inv_pos.mpr (pow_pos hUpos 2)
  have hdec := tendsto_quadraticExponential_mul_geometric
    (a := ‖q‖) (b := (‖U‖ ^ 2)⁻¹) (norm_nonneg q) hq hb
  have hdec' : Filter.Tendsto
      (fun n : ℕ => ‖U‖⁻¹ * (‖q‖ ^ (n * (n + 1) / 2) * ((‖U‖ ^ 2)⁻¹) ^ n))
      Filter.atTop (nhds 0) := by
    simpa using hdec.const_mul ‖U‖⁻¹
  have hnorm : (fun n : ℕ => ‖oddThetaTerm q U (-(n : ℤ) - 1)‖) =
      fun n : ℕ => ‖U‖⁻¹ * (‖q‖ ^ (n * (n + 1) / 2) * ((‖U‖ ^ 2)⁻¹) ^ n) := by
    funext n
    rw [norm_oddThetaTerm_neg_nat q U hU n]
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  exact (tendsto_zero_iff_norm_tendsto_zero).mpr (by
    rw [hnorm]
    exact hdec')

/-- The full two-sided odd theta series is summable, combining the forward half
with the negative half. -/
theorem summable_oddThetaTerm (q U : L) (hU : U ≠ 0) (hq : ‖q‖ < 1) :
    Summable (fun n : ℤ => oddThetaTerm q U n) := by
  refine Summable.of_nat_of_neg_add_one (f := fun n : ℤ => oddThetaTerm q U n) ?_ ?_
  · exact summable_oddThetaTerm_nat q U hU hq
  · simpa [Int.cast_add, Int.cast_one, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using summable_oddThetaTerm_neg_nat q U hU hq

/-! ## 5. Root and packet normalization records (no choice of root) -/

/-- A supplied square root of q: the shift law of EtTh Proposition 1.4 is stated
for r with r^2 = q, but the library never chooses such a root.  Callers must
provide r and the proof r^2 = q (and r is automatically nonzero when q is). -/
structure OddThetaRootData (q : L) where
  /-- the square root of q -/
  r : L
  /-- the square-root equation -/
  r_sq : r ^ 2 = q
  /-- q is nonzero -/
  q_ne_zero : q ≠ 0

/-- The root is nonzero. -/
theorem OddThetaRootData.r_ne_zero {q : L} (h : OddThetaRootData q) : h.r ≠ 0 := by
  intro hr
  apply h.q_ne_zero
  rw [← h.r_sq, hr]
  simp

/-- The root-existence condition 2*l | v(q) of the source normalization: the
packet asks for an l-th root of a prescribed q-parameter, which exists only when
2*l divides the valuation of q (recorded as data, not chosen).  The structure
only records the divisibility datum; the construction of the root from it is the
remaining valuation-theoretic obligation. -/
structure OddThetaRootExistenceData (q : L) where
  /-- the l of the packet -/
  l : ℕ
  /-- l is positive -/
  l_pos : 0 < l
  /-- the integral valuation of q in the packet normalization -/
  vq : ℤ
  /-- the root-existence divisibility condition 2*l | v(q) -/
  dvd_vq : (2 * (l : ℤ)) ∣ vq

/-- The packet normalization ratio record: the real analytic packet uses
q = 1/5, while the nonarchimedean series uses a parameter q with |q| < 1 and a
supplied square root r.  The two normalizations are recorded separately and are
NOT identified: |r| may differ from 1/5 (indeed |r|^2 = |q|). -/
structure OddThetaPacketNormalization (q : L) where
  /-- the packet ratio 1/5 as a real number -/
  packet_ratio : ℝ
  /-- the packet ratio is exactly 1/5 -/
  packet_ratio_eq : packet_ratio = 1 / 5
  /-- the nonarchimedean norm of q is strictly below one -/
  norm_q_lt_one : ‖q‖ < 1
  /-- the nonarchimedean norm of a square root r of q is its square root norm -/
  root : OddThetaRootData q
  /-- |r|^2 = |q| -/
  norm_root_sq : ‖root.r‖ ^ 2 = ‖q‖

end LeanFormal.IUT.Foundations.Theta
