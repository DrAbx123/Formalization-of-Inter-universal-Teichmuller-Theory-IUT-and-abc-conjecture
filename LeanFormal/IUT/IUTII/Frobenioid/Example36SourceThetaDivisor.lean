/-
  # Theta units, nonvanishing and q-adic divisor data at the Example 3.6 carrier

  N8 Layer 1 (n8-layer1-build-20261020), theta-divisor branch.  This module
  constructs the theta unit / nonvanishing / q-adic divisor data that is
  actually available from the analytic Jacobi theta function of
  `Example36ThetaSeries` and the analytic carrier of
  `Example36SourceThetaGenerator`, and states the remaining source-theta
  divisor gap exactly.

  ## 1. Analytic theta value on every carrier (not only q = 1/5)

  For an analytic carrier `t` (`0 < t.q < 1`) we define the normalisation point
  `carrierThetaTau t = i * log(1/q)/pi`, prove `exp(pi i tau) = q`
  (`carrierThetaTau_exp`), and define
  `analyticThetaValue t = jacobiTheta (carrierThetaTau t)`.

  We then prove the one-sided q-expansion

    `analyticThetaValue t = 1 + 2 * sum_{n >= 0} q ^ ((n+1)^2)`

  (`analyticThetaValue_eq_tsum_nat`), identify it with the complexification of
  the real series `thetaRealValue t = 1 + 2 * sum_{n >= 0} q ^ ((n+1)^2)`
  (`analyticThetaValue_eq_ofReal`), and prove that this real series is
  summable and strictly positive.  Hence `analyticThetaValue t != 0` for every
  carrier, not only at q = 1/5.  At q = 1/5 the value is exactly Mathlib's
  `jacobiThetaQ` (`analyticThetaValue_concrete_eq_jacobiThetaQ`).

  ## 2. Theta as a principal unit: q-adic valuation zero

  The same one-sided expansion shows

    `analyticThetaValue t = 1 + q * thetaQAdicQuotient t`

  with `thetaQAdicQuotient t = 2 * sum_{n >= 0} q ^ ((n+1)^2 - 1) > 0`
  (`analyticThetaValue_eq_one_add_q_mul`, `thetaQAdicQuotient_pos`).  Thus the
  reduction of theta modulo q is the unit 1: theta is a principal unit whose
  q-adic valuation is zero.  At the formal level the q-expansion multiplicity
  series `gaussianThetaFormalSeries` (coefficient of X^m = number of integers
  n with n^2 = m, realised on the finite interval [-m, m]) has constant
  coefficient 1, is a unit of `PowerSeries ℤ`, and has `PowerSeries.order = 0`
  (`gaussianThetaFormalSeries_isUnit`, `gaussianThetaFormalSeries_order`).

  ## 3. The zero divisor on the q-disc is empty

  Since `analyticThetaValue t` is the complexification of the strictly positive
  real number `thetaRealValue t`, the zero set of the analytic theta function on
  the carrier is empty (`analyticThetaZeroSet_empty`): the zero divisor of the
  even theta q-series on the q-disc is trivial.

  This is a statement about the even theta q-series only.  It is NOT the source
  theta divisor of EtTh Proposition 1.4 (i): the source theta function
  `Theta(U) = q^(-1/8) * sum_n (-1)^n q^((n+1/2)^2/2) U^(2n+1)` is the odd
  theta function, whose divisor has zeros at the cusps (multiplicity one) and
  poles equal to D_1.  The gap is stated precisely in Section 6.

  ## 4. Units and roots: thetaUnit, thetaRootValue, normalizedTheta

  On the carrier we define the positive real units
  `thetaQUnit t` (the q-parameter) and `thetaUnit t j = realThetaValue t.q j`
  (the label-j theta value), and prove:

  * `thetaUnit_eq_qUnit_pow`: `thetaUnit t j = (thetaQUnit t) ^ (j^2)`;
  * `thetaUnit_neg`: label negation acts trivially, matching `realThetaValue_neg`;
  * `thetaUnit_transport`: the q -> q^2 transport squares every theta value;
  * `thetaUnit_concrete_packetScale`: at q = 1/5 the unit is exactly the
    concrete source theater packet scale.

  For roots we define `thetaRootValue r j = r ^ (j^2)`.  If `r ^ (2*l) = q`
  then `thetaRootValue r j` is a `2*l`-th root of `realThetaValue q j`
  (`thetaRootValue_twoLth_root`), and multiplying `r` by a `2*l`-th root of
  unity `zeta` multiplies the root value by `zeta ^ (j^2)`, itself a `2*l`-th
  root of unity (`thetaRootValue_mul_root_of_pow_eq_one`).  This is the
  actually constructed mu_(2l)-orbit action on the real theta values.  The
  square-root case is realised concretely with `Real.sqrt gaussianFiveThetaQ`
  (`thetaRootValue_sqrt_concrete_sq_complex`, matching `qExpansionTerm`).

  What is NOT constructed: the choice of a theta root in the value group, the
  root-existence condition `2*l | v(q)` for the nonarchimedean packet, the
  Kummer class of theta, and the actual mu_(2l)-torsor / Theta-link.  The
  hypotheses `r ^ (2*l) = q` are supplied data, never chosen by this file.

  ## 5. The q-adic order-zero part of the odd theta series

  Using the actual `oddThetaTerm` of `Foundations/Theta/OddTheta.lean` we prove
  that the theta exponent `n(n+1)/2` vanishes exactly for `n = 0` and
  `n = -1` (`oddThetaExponent_eq_zero_iff`), that the sum of the two
  order-zero terms is `U - U^(-1)` (`oddThetaOrderZeroPart_eq`), and that
  `U - U^(-1)` has simple zeros exactly at `U = 1` and `U = -1`
  (`oddThetaReduction_eq_zero_iff`, with the factorisations exhibiting
  multiplicity one) and a simple pole at `U = 0`
  (`oddThetaReduction_pole_value`).  This is the order-zero (`mod q`) reduction
  of the odd theta series, i.e. exactly the special-fibre restriction
  `U - U^(-1)` used in the proof of EtTh Proposition 1.4 (i) on the irreducible
  component labelled 0, and nothing more.

  ## 6. Exact remaining source theta divisor / line bundle gap

  The following statements of EtTh Proposition 1.4 are NOT proved here and no
  object of this file is claimed to replace them:

  (a) convergence/reindexing of the full two-sided nonarchimedean series
      `sum_{n in Z} oddThetaTerm q U n` (OddTheta.lean currently proves only the
      forward half `n >= 0`; the negative half and the two-sided sum are open);
  (b) the shift law `Theta(q^(a/2) U) = (-1)^a q^(-a^2/2) U^(-2a) Theta(U)`
      for a chosen square root of q, and the nonvanishing of the odd theta at
      `U = i` (EtTh Proposition 1.4 (ii));
  (c) the meromorphic continuation of the odd theta function to the Tate curve
      `Yddot` and its divisor: zeros precisely at the cusps, each of
      multiplicity one, and pole divisor precisely `D_1`
      (EtTh Proposition 1.4 (i));
  (d) the identification of the Kummer classes of Proposition 1.3 with the
      values of the theta function (`O_K^times`-multiples), i.e. the actual
      "etale theta function" (EtTh Proposition 1.4 (iii)), together with the
      line-bundle section and the nontrivial source Theta-link.

  In particular, the empty zero divisor proved for the even theta q-series in
  Section 3 is not the source theta divisor, and comparing q-series
  coefficients cannot establish (c) or (d).

  Source correspondence: EtTh Proposition 1.4 (i), (ii) and (iii); IUT II,
  theta evaluation and q-expansion; IUT I, Definition 3.6, Corollary 3.7.
-/

import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceThetaGenerator
import LeanFormal.IUT.IUTII.Frobenioid.Example36ThetaSeries
import LeanFormal.IUT.Foundations.Theta.OddTheta
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Inverse

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace SourceThetaDivisor

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator
open LeanFormal.IUT.IUTII.Frobenioid.Example36.ThetaSeries
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open LeanFormal.IUT.Foundations.Theta

noncomputable section

/-! ## 1. The theta normalisation point attached to a carrier -/

/-- The theta normalisation point of an analytic carrier:
`tau = i * log(1/q)/pi`, so that `exp(pi i tau) = q`. -/
noncomputable def carrierThetaTau (t : AnalyticThetaCarrier) : ℂ :=
  ((Real.log (1 / t.q) / Real.pi : ℝ) : ℂ) * Complex.I

theorem carrierThetaTau_im (t : AnalyticThetaCarrier) :
    (carrierThetaTau t).im = Real.log (1 / t.q) / Real.pi := by
  unfold carrierThetaTau
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem carrierThetaTau_im_pos (t : AnalyticThetaCarrier) :
    0 < (carrierThetaTau t).im := by
  rw [carrierThetaTau_im]
  exact div_pos (Real.log_pos (one_lt_one_div t.q_pos t.q_lt_one)) Real.pi_pos

theorem carrierThetaTau_core (t : AnalyticThetaCarrier) :
    Real.pi * Complex.I * carrierThetaTau t =
      -((Real.log (1 / t.q) : ℝ) : ℂ) := by
  unfold carrierThetaTau
  rw [show (Real.log (1 / t.q) / Real.pi : ℝ) =
      (Real.log (1 / t.q) : ℂ) / (Real.pi : ℂ) from by
    push_cast
    ring]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  rw [Complex.I_sq]
  ring

/-- The defining property of the theta normalisation point: `exp(pi i tau) = q`. -/
theorem carrierThetaTau_exp (t : AnalyticThetaCarrier) :
    Complex.exp (Real.pi * Complex.I * carrierThetaTau t) = (t.q : ℂ) := by
  rw [carrierThetaTau_core, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  congr 1
  rw [Real.exp_neg, Real.exp_log (div_pos one_pos t.q_pos), one_div, inv_inv]

/-- The n-th summand of the one-sided Mathlib Jacobi theta expansion at the
carrier normalisation point is the q-power `q ^ ((n+1)^2)`. -/
theorem carrierTheta_term_eq (t : AnalyticThetaCarrier) (n : ℕ) :
    Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * carrierThetaTau t) =
      (t.q : ℂ) ^ ((n + 1) ^ 2) := by
  have harg : Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * carrierThetaTau t =
      (((n + 1) ^ 2 : ℕ) : ℂ) * (Real.pi * Complex.I * carrierThetaTau t) := by
    push_cast
    ring
  rw [harg, Complex.exp_nat_mul, carrierThetaTau_exp]

/-! ## 2. The analytic theta value and its q-expansion -/

/-- The analytic theta value attached to an analytic carrier: Mathlib's actual
one-variable Jacobi theta function at the normalisation point. -/
noncomputable def analyticThetaValue (t : AnalyticThetaCarrier) : ℂ :=
  jacobiTheta (carrierThetaTau t)

/-- **One-sided q-expansion of the analytic theta value.**  For every carrier
`t` with `0 < q < 1`, the analytic theta value is
`1 + 2 * sum_{n >= 0} q ^ ((n+1)^2)`. -/
theorem analyticThetaValue_eq_tsum_nat (t : AnalyticThetaCarrier) :
    analyticThetaValue t =
      1 + 2 * ∑' n : ℕ, (t.q : ℂ) ^ ((n + 1) ^ 2) := by
  rw [analyticThetaValue, jacobiTheta_eq_tsum_nat (carrierThetaTau_im_pos t)]
  congrm 1 + 2 * ?_
  exact tsum_congr (fun n => carrierTheta_term_eq t n)

/-- The real theta series attached to the carrier:
`thetaRealValue t = 1 + 2 * sum_{n >= 0} q ^ ((n+1)^2)`. -/
noncomputable def thetaRealValue (t : AnalyticThetaCarrier) : ℝ :=
  1 + 2 * ∑' n : ℕ, t.q ^ ((n + 1) ^ 2)

/-- Summability of the one-sided positive theta series. -/
theorem summable_thetaNatTerm (t : AnalyticThetaCarrier) :
    Summable (fun n : ℕ => t.q ^ ((n + 1) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun n => pow_nonneg t.q_pos.le _) (fun n => ?_)
    (summable_geometric_of_lt_one t.q_pos.le t.q_lt_one)
  refine pow_le_pow_of_le_one t.q_pos.le t.q_lt_one.le ?_
  calc n ≤ n + 1 := Nat.le_succ n
    _ ≤ (n + 1) * (n + 1) := Nat.le_mul_self (n + 1)
    _ = (n + 1) ^ 2 := (pow_two (n + 1)).symm

/-- The one-sided positive theta sum is strictly positive: it is at least its
first summand `q > 0`. -/
theorem thetaNatSum_pos (t : AnalyticThetaCarrier) :
    0 < ∑' n : ℕ, t.q ^ ((n + 1) ^ 2) := by
  have h := Summable.sum_le_tsum ({0} : Finset ℕ)
    (fun i _ => pow_nonneg t.q_pos.le _) (summable_thetaNatTerm t)
  have h0 : 0 < t.q ^ ((0 + 1) ^ 2) := by simpa using t.q_pos
  exact lt_of_lt_of_le h0 (by simpa using h)

/-- The real theta value is strictly positive. -/
theorem thetaRealValue_pos (t : AnalyticThetaCarrier) : 0 < thetaRealValue t := by
  have h := thetaNatSum_pos t
  unfold thetaRealValue
  linarith

/-- **The analytic theta value is the complexification of the real theta
value.** -/
theorem analyticThetaValue_eq_ofReal (t : AnalyticThetaCarrier) :
    analyticThetaValue t = (thetaRealValue t : ℂ) := by
  rw [analyticThetaValue_eq_tsum_nat, thetaRealValue, Complex.ofReal_add,
    Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_tsum]
  congr 1
  congr 1
  exact tsum_congr (fun n => (Complex.ofReal_pow t.q ((n + 1) ^ 2)).symm)

/-- **Nonvanishing of the analytic theta value at every carrier.** -/
theorem analyticThetaValue_ne_zero (t : AnalyticThetaCarrier) :
    analyticThetaValue t ≠ 0 := by
  rw [analyticThetaValue_eq_ofReal]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (thetaRealValue_pos t))

theorem analyticThetaValue_re (t : AnalyticThetaCarrier) :
    (analyticThetaValue t).re = thetaRealValue t := by
  rw [analyticThetaValue_eq_ofReal]
  exact Complex.ofReal_re (thetaRealValue t)

/-- The concrete carrier sits at the same normalisation point as
`Example36ThetaSeries`, hence its analytic theta value is exactly
`jacobiThetaQ`. -/
theorem analyticThetaValue_concrete_eq_jacobiThetaQ :
    analyticThetaValue analyticThetaCarrierConcrete = jacobiThetaQ := by
  have hq : (1 : ℝ) / analyticThetaCarrierConcrete.q = 5 := by
    rw [analyticThetaCarrierConcrete_q, gaussianFiveThetaQ_eq_inv_five]
    norm_num
  unfold analyticThetaValue jacobiThetaQ carrierThetaTau thetaTau
  rw [hq]

/-- At q = 1/5 the analytic theta value is nonzero (a second proof, through the
general carrier theorem, of the existing `jacobiThetaQ_ne_zero`). -/
theorem analyticTheta_ne_zero_concrete :
    analyticThetaValue analyticThetaCarrierConcrete ≠ 0 :=
  analyticThetaValue_ne_zero analyticThetaCarrierConcrete

/-! ## 3. Theta as a principal unit: q-adic valuation zero -/

/-- The quotient `(theta - 1)/q` of the analytic theta value, i.e. the value of
the theta q-expansion after factoring out the q-parameter:
`2 * sum_{n >= 0} q ^ ((n+1)^2 - 1)`. -/
noncomputable def thetaQAdicQuotient (t : AnalyticThetaCarrier) : ℝ :=
  2 * ∑' n : ℕ, t.q ^ ((n + 1) ^ 2 - 1)

/-- Summability of the q-adic quotient series. -/
theorem summable_thetaQAdicQuotientTerm (t : AnalyticThetaCarrier) :
    Summable (fun n : ℕ => t.q ^ ((n + 1) ^ 2 - 1)) := by
  refine Summable.of_nonneg_of_le (fun n => pow_nonneg t.q_pos.le _) (fun n => ?_)
    (summable_geometric_of_lt_one t.q_pos.le t.q_lt_one)
  refine pow_le_pow_of_le_one t.q_pos.le t.q_lt_one.le ?_
  have h1 : n + 1 ≤ (n + 1) ^ 2 := by
    calc n + 1 ≤ (n + 1) * (n + 1) := Nat.le_mul_self (n + 1)
      _ = (n + 1) ^ 2 := (pow_two (n + 1)).symm
  exact Nat.le_sub_one_of_lt (Nat.lt_of_succ_le h1)

/-- The q-adic quotient is strictly positive. -/
theorem thetaQAdicQuotient_pos (t : AnalyticThetaCarrier) :
    0 < thetaQAdicQuotient t := by
  have h := Summable.sum_le_tsum ({0} : Finset ℕ)
    (fun i _ => pow_nonneg t.q_pos.le _) (summable_thetaQAdicQuotientTerm t)
  have h0 : 0 < t.q ^ ((0 + 1) ^ 2 - 1) := by norm_num
  have hS : 0 < ∑' n : ℕ, t.q ^ ((n + 1) ^ 2 - 1) :=
    lt_of_lt_of_le h0 (by simpa using h)
  unfold thetaQAdicQuotient
  linarith

/-- **The real theta series as a principal unit**: `theta = 1 + q * u` with the
explicit positive quotient `u = thetaQAdicQuotient t`. -/
theorem thetaRealValue_eq_one_add_q_mul (t : AnalyticThetaCarrier) :
    thetaRealValue t = 1 + t.q * thetaQAdicQuotient t := by
  have hsum : (∑' n : ℕ, t.q ^ ((n + 1) ^ 2)) =
      t.q * ∑' n : ℕ, t.q ^ ((n + 1) ^ 2 - 1) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    rw [← pow_succ']
    rw [Nat.sub_add_cancel (Nat.one_le_pow 2 (n + 1) (Nat.succ_pos n))]
  unfold thetaRealValue thetaQAdicQuotient
  rw [hsum]
  ring

/-- **The analytic theta value is a principal unit at q = 0**:
`theta = 1 + q * u` with `u` the positive real quotient
`thetaQAdicQuotient t`.  In particular the reduction of theta modulo q is the
unit `1`, so the q-adic valuation of theta is zero. -/
theorem analyticThetaValue_eq_one_add_q_mul (t : AnalyticThetaCarrier) :
    analyticThetaValue t = 1 + (t.q : ℂ) * (thetaQAdicQuotient t : ℂ) := by
  rw [analyticThetaValue_eq_ofReal, thetaRealValue_eq_one_add_q_mul]
  push_cast
  ring

/-- The q-adic quotient is nonzero. -/
theorem thetaQAdicQuotient_ne_zero (t : AnalyticThetaCarrier) :
    thetaQAdicQuotient t ≠ 0 :=
  ne_of_gt (thetaQAdicQuotient_pos t)

/-- **Concrete q-adic unit statement at q = 1/5.**  Mathlib's actual Jacobi
theta value at q = 1/5 is `1 + (1/5) * u` with a strictly positive real `u`. -/
theorem jacobiThetaQ_eq_one_add_q_mul :
    jacobiThetaQ =
      1 + (gaussianFiveThetaQ : ℂ) *
        (thetaQAdicQuotient analyticThetaCarrierConcrete : ℂ) := by
  rw [← analyticThetaValue_concrete_eq_jacobiThetaQ]
  exact analyticThetaValue_eq_one_add_q_mul analyticThetaCarrierConcrete

/-! ## 4. The formal q-expansion multiplicity series and its q-adic order -/

/-- The multiplicity of `m` as a Gaussian exponent `n^2` over the integers,
realised on the finite interval `[-m, m]` (every `n` with `n^2 = m` satisfies
`|n| <= m`). -/
noncomputable def gaussianThetaCoeff (m : ℕ) : ℕ :=
  ((Finset.Icc (-(m : ℤ)) (m : ℤ)).filter (fun n => gaussExponent n = (m : ℤ))).card

/-- The multiplicity of exponent zero is one (only `n = 0`). -/
theorem gaussianThetaCoeff_zero : gaussianThetaCoeff 0 = 1 := by
  simp [gaussianThetaCoeff, gaussExponent, Finset.filter_singleton]

/-- **The formal theta q-expansion**: the power series whose `m`-th coefficient
is the number of integers `n` with `n^2 = m`. -/
noncomputable def gaussianThetaFormalSeries : PowerSeries ℤ :=
  PowerSeries.mk (fun m => (gaussianThetaCoeff m : ℤ))

@[simp] theorem gaussianThetaFormalSeries_coeff (m : ℕ) :
    PowerSeries.coeff m gaussianThetaFormalSeries = (gaussianThetaCoeff m : ℤ) := by
  simp [gaussianThetaFormalSeries]

/-- The constant coefficient of the formal theta q-series is `1`. -/
theorem gaussianThetaFormalSeries_constantCoeff :
    PowerSeries.constantCoeff gaussianThetaFormalSeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, gaussianThetaFormalSeries_coeff,
    gaussianThetaCoeff_zero]
  norm_num

/-- **The formal theta q-series is a unit of `PowerSeries ℤ`.** -/
theorem gaussianThetaFormalSeries_isUnit : IsUnit gaussianThetaFormalSeries := by
  rw [PowerSeries.isUnit_iff_constantCoeff, gaussianThetaFormalSeries_constantCoeff]
  exact isUnit_one

/-- **The q-adic order of the formal theta q-series is zero.** -/
theorem gaussianThetaFormalSeries_order :
    PowerSeries.order gaussianThetaFormalSeries = 0 := by
  change PowerSeries.order gaussianThetaFormalSeries = ((0 : ℕ) : ℕ∞)
  rw [PowerSeries.order_eq_nat]
  constructor
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
      gaussianThetaFormalSeries_constantCoeff]
    norm_num
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)

/-- The formal coefficient is positive exactly when the exponent is realised by
an integer. -/
theorem gaussianThetaCoeff_pos_iff (m : ℕ) :
    0 < gaussianThetaCoeff m ↔ ∃ n : ℤ, gaussExponent n = (m : ℤ) := by
  unfold gaussianThetaCoeff
  rw [Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨n, _, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    have habs : |n| ≤ (m : ℤ) := by
      have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
      have hsq : |n| ^ 2 = (m : ℤ) := by
        rw [sq_abs, ← gaussExponent, hn]
      rcases eq_or_lt_of_le hm with hm0 | hmpos
      · have hzero : |n| = 0 := by
          have hsq0 : |n| ^ 2 = 0 := by rw [hsq, hm0.symm]
          exact sq_eq_zero_iff.mp hsq0
        rw [hzero]
        exact hm0.le
      · have h1 : 1 ≤ |n| := by
          by_contra hlt
          push Not at hlt
          have hle : |n| ≤ 0 := by omega
          have hzero : |n| = 0 := le_antisymm hle (abs_nonneg n)
          rw [hzero] at hsq
          norm_num at hsq
          omega
        nlinarith [hsq, h1, abs_nonneg n]
    exact ⟨n, by rw [Finset.mem_Icc]; exact abs_le.mp habs, hn⟩

/-! ## 5. The zero divisor on the q-disc is empty -/

/-- The zero set of the analytic theta function on the q-carrier. -/
def analyticThetaZeroSet : Set ℝ :=
  {x | ∃ t : AnalyticThetaCarrier, t.q = x ∧ analyticThetaValue t = 0}

/-- **The zero divisor of the even theta q-series on the q-disc is trivial**:
the analytic theta value never vanishes on the carrier. -/
theorem analyticThetaZeroSet_empty : analyticThetaZeroSet = ∅ := by
  ext x
  simp only [analyticThetaZeroSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
    not_exists, not_and]
  intro t _ h
  exact analyticThetaValue_ne_zero t h

/-- **The zero divisor of the even theta q-series is trivial.**  Combining the
explicit principal-unit form and the empty zero set: theta is a q-adic unit and
has no zeros on the positive real q-disc. -/
theorem analyticThetaDivisor_trivial (t : AnalyticThetaCarrier) :
    analyticThetaValue t ≠ 0 ∧
      analyticThetaValue t = 1 + (t.q : ℂ) * (thetaQAdicQuotient t : ℂ) :=
  ⟨analyticThetaValue_ne_zero t, analyticThetaValue_eq_one_add_q_mul t⟩

/-! ## 6. Units and roots of the theta values -/

/-- The q-parameter as a positive real unit. -/
def thetaQUnit (t : AnalyticThetaCarrier) : ℝˣ :=
  Units.mk0 t.q (ne_of_gt t.q_pos)

/-- The label-`j` Gaussian theta value as a positive real unit. -/
def thetaUnit (t : AnalyticThetaCarrier) (j : ℤ) : ℝˣ :=
  Units.mk0 (realThetaValue t.q j) (ne_of_gt (realThetaValue_pos t.q_pos j))

@[simp] theorem thetaQUnit_apply (t : AnalyticThetaCarrier) :
    (thetaQUnit t : ℝ) = t.q :=
  rfl

@[simp] theorem thetaUnit_apply (t : AnalyticThetaCarrier) (j : ℤ) :
    (thetaUnit t j : ℝ) = realThetaValue t.q j :=
  rfl

/-- The theta unit at label `j` is the `j^2`-th power of the q-unit. -/
theorem thetaUnit_eq_qUnit_pow (t : AnalyticThetaCarrier) (j : ℤ) :
    thetaUnit t j = thetaQUnit t ^ (gaussExponent j).toNat := by
  ext
  simp [thetaUnit, thetaQUnit, realThetaValue]

/-- Label negation acts trivially on the theta unit, matching
`realThetaValue_neg`. -/
theorem thetaUnit_neg (t : AnalyticThetaCarrier) (j : ℤ) :
    thetaUnit t (-j) = thetaUnit t j := by
  ext
  simp [thetaUnit, realThetaValue]

/-- The theta unit at label zero is one. -/
theorem thetaUnit_zero (t : AnalyticThetaCarrier) : thetaUnit t 0 = 1 := by
  ext
  simp [thetaUnit]

/-- The theta value at a power `q^a` of the q-parameter is the `a`-th power of
the theta value at `q`. -/
theorem realThetaValue_pow_q (q : ℝ) (a : ℕ) (j : ℤ) :
    realThetaValue (q ^ a) j = (realThetaValue q j) ^ a := by
  simp only [realThetaValue]
  simp only [← pow_mul]
  rw [Nat.mul_comm a]

/-- **Power-orbit compatibility**: the analytic transport `q -> q^2` squares
every theta unit. -/
theorem thetaUnit_transport (t : AnalyticThetaCarrier) (j : ℤ) :
    thetaUnit (analyticThetaTransport t) j = thetaUnit t j ^ 2 := by
  ext
  simp only [thetaUnit, Units.val_mk0, Units.val_pow_eq_pow_val, analyticThetaTransport]
  exact realThetaValue_pow_q t.q 2 j

/-- At q = 1/5 the theta unit is exactly the concrete source theater packet
scale. -/
theorem thetaUnit_concrete_packetScale (l : PrimeGeFive) (j : SignedLabel l.value) :
    ((thetaUnit analyticThetaCarrierConcrete j.1 : ℝˣ) : ℝ) =
      (sourceTheater l).thetaPacket.scale j := by
  rw [thetaUnit_apply, analyticThetaCarrierConcrete_q]
  exact (sourceTheater_theta_scale l j).symm

/-- The root theta value at label `j`: `r ^ (j^2)`.  The root `r` is supplied
data; the file never chooses one. -/
noncomputable def thetaRootValue (r : ℝ) (j : ℤ) : ℝ :=
  r ^ (gaussExponent j).toNat

/-- A `2*l`-th root `r` of `q` produces a `2*l`-th root of every theta value. -/
theorem thetaRootValue_twoLth_root (r : ℝ) (l : ℕ) (j : ℤ) :
    thetaRootValue r j ^ (2 * l) = realThetaValue (r ^ (2 * l)) j := by
  simp only [thetaRootValue, realThetaValue]
  simp only [← pow_mul]
  rw [Nat.mul_comm _ (2 * l)]

/-- The square-root case: the square of the root theta value is the theta value
at `r^2`. -/
theorem thetaRootValue_sq (r : ℝ) (j : ℤ) :
    thetaRootValue r j ^ 2 = realThetaValue (r ^ 2) j := by
  simpa using thetaRootValue_twoLth_root r 1 j

/-- Multiplying the root by a `2*l`-th root of unity multiplies the root theta
value by `zeta ^ (j^2)`, which is again a `2*l`-th root of unity.  This is the
actually constructed `mu_(2l)`-orbit action on the real theta values. -/
theorem thetaRootValue_mul_root_of_pow_eq_one (ζ r : ℝ) (l : ℕ)
    (hζ : ζ ^ (2 * l) = 1) (j : ℤ) :
    thetaRootValue (ζ * r) j = (ζ ^ (gaussExponent j).toNat) * thetaRootValue r j ∧
      (ζ ^ (gaussExponent j).toNat) ^ (2 * l) = 1 := by
  constructor
  · simp only [thetaRootValue]
    rw [mul_pow]
  · simp only [← pow_mul]
    rw [Nat.mul_comm _ (2 * l), pow_mul, hζ, one_pow]

/-- The sign ambiguity of the square root: negating the supplied square root
multiplies the root theta value by `(-1)^(j^2)`, which is `(-1)^j`. -/
theorem thetaRootValue_neg_root (r : ℝ) (j : ℤ) :
    thetaRootValue (-r) j = ((-1 : ℝ) ^ (gaussExponent j).toNat) * thetaRootValue r j := by
  have h := thetaRootValue_mul_root_of_pow_eq_one (-1) r 1 (by norm_num) j
  simpa using h.1

/-- The concrete square root of the Example 3.6 q-parameter. -/
theorem thetaRootValue_sqrt_concrete_sq (j : ℤ) :
    thetaRootValue (Real.sqrt gaussianFiveThetaQ) j ^ 2 =
      realThetaValue gaussianFiveThetaQ j := by
  rw [thetaRootValue_sq, Real.sq_sqrt gaussianFiveThetaQ_pos.le]

/-- The concrete root theta value matches the actual q-expansion term
`qExpansionTerm` after squaring and complexifying. -/
theorem thetaRootValue_sqrt_concrete_sq_complex (j : ℤ) :
    ((thetaRootValue (Real.sqrt gaussianFiveThetaQ) j ^ 2 : ℝ) : ℂ) =
      qExpansionTerm j := by
  rw [thetaRootValue_sqrt_concrete_sq]
  exact (qExpansionTerm_eq_ofReal j).symm

/-- The normalised theta unit: the theta unit at label `j` divided by the theta
unit at label `0` (which is one). -/
def normalizedTheta (t : AnalyticThetaCarrier) (j : ℤ) : ℝˣ :=
  thetaUnit t j / thetaUnit t 0

theorem normalizedTheta_apply (t : AnalyticThetaCarrier) (j : ℤ) :
    (normalizedTheta t j : ℝ) = realThetaValue t.q j := by
  simp [normalizedTheta, thetaUnit]

theorem normalizedTheta_eq_thetaUnit (t : AnalyticThetaCarrier) (j : ℤ) :
    normalizedTheta t j = thetaUnit t j := by
  simp [normalizedTheta, thetaUnit_zero]

/-- **Orbit compatibility of the normalised theta unit.**  The `q -> q^2`
transport squares the normalised theta value, and for every supplied
`2*l`-th root `r` of `q` the root theta value is a `2*l`-th root of the
normalised theta value. -/
theorem normalizedTheta_orbit_compatible (t : AnalyticThetaCarrier) (j : ℤ)
    (r : ℝ) (l : ℕ) (hr : r ^ (2 * l) = t.q) :
    normalizedTheta (analyticThetaTransport t) j = normalizedTheta t j ^ 2 ∧
      thetaRootValue r j ^ (2 * l) = (normalizedTheta t j : ℝ) := by
  constructor
  · rw [normalizedTheta_eq_thetaUnit, normalizedTheta_eq_thetaUnit]
    exact thetaUnit_transport t j
  · rw [thetaRootValue_twoLth_root, hr, normalizedTheta_apply]

/-! ## 7. The q-adic order-zero part of the odd theta series -/

section OddThetaQAdic

variable {L : Type*} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- The sum of the two odd-theta terms of q-adic order zero
(`n = 0` and `n = -1`). -/
noncomputable def oddThetaOrderZeroPart (q U : L) : L :=
  oddThetaTerm q U 0 + oddThetaTerm q U (-1)

/-- The q-adic order-zero part of the odd theta series is `U - U^(-1)`. -/
theorem oddThetaOrderZeroPart_eq (q U : L) :
    oddThetaOrderZeroPart q U = U - U⁻¹ := by
  simp [oddThetaOrderZeroPart, sub_eq_add_neg]

/-- The theta exponent `n(n+1)/2` vanishes exactly for `n = 0` and `n = -1`. -/
theorem oddThetaExponent_eq_zero_iff (n : ℤ) :
    oddThetaExponent n = 0 ↔ n = 0 ∨ n = -1 := by
  have hcoe : (oddThetaExponent n : ℤ) = n * (n + 1) / 2 := oddThetaExponent_coe n
  constructor
  · intro h
    have hdiv : n * (n + 1) / 2 = 0 := by
      rw [← hcoe, h]
      rfl
    have hnonneg : 0 ≤ n * (n + 1) := by
      by_cases h0 : 0 ≤ n
      · exact mul_nonneg h0 (by linarith)
      · push Not at h0
        exact mul_nonneg_of_nonpos_of_nonpos h0.le (by linarith)
    have hlt : n * (n + 1) < 2 := by
      by_contra hge
      push Not at hge
      have hpos : 1 ≤ n * (n + 1) / 2 := by omega
      omega
    have hprod : n * (n + 1) = 0 ∨ n * (n + 1) = 1 := by omega
    rcases hprod with hp | hp
    · rcases mul_eq_zero.mp hp with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (by omega)
    · have heven : Even (n * (n + 1)) := Int.even_mul_succ_self n
      rw [hp] at heven
      norm_num at heven
  · rintro (rfl | rfl) <;> simp

/-- Every odd theta term other than the two order-zero terms has q-adic
exponent at least one. -/
theorem oddThetaExponent_pos_of_ne_zero_of_ne_neg_one (n : ℤ)
    (h0 : n ≠ 0) (h1 : n ≠ -1) : 0 < oddThetaExponent n := by
  refine Nat.pos_of_ne_zero (fun h => ?_)
  rcases (oddThetaExponent_eq_zero_iff n).mp h with h' | h'
  · exact h0 h'
  · exact h1 h'

/-- **The `mod q` reduction of the odd theta series on the special fibre**:
the terms of q-adic order zero sum to `U - U^(-1)`.  This is exactly the
special-fibre restriction used in the proof of EtTh Proposition 1.4 (i) on the
component labelled `0`; it is a statement about the order-zero terms only, not
about the meromorphic theta divisor. -/
theorem oddTheta_qAdic_orderZero_reduction (q U : L) :
    oddThetaTerm q U 0 + oddThetaTerm q U (-1) = U - U⁻¹ :=
  oddThetaOrderZeroPart_eq q U

end OddThetaQAdic

/-! ## 8. Zeros and the pole of the order-zero special-fibre function -/

section FieldReduction

variable {K : Type*} [Field K]

/-- The factorisation `U - U^(-1) = U^(-1) (U - 1)(U + 1)`. -/
theorem oddThetaReduction_factorization (U : K) (hU : U ≠ 0) :
    U - U⁻¹ = U⁻¹ * (U - 1) * (U + 1) := by
  field_simp [hU]
  ring

/-- The order-zero special-fibre function vanishes exactly at `U = ±1`. -/
theorem oddThetaReduction_eq_zero_iff (U : K) (hU : U ≠ 0) :
    U - U⁻¹ = 0 ↔ U = 1 ∨ U = -1 := by
  constructor
  · intro h
    have hmul : U * (U - U⁻¹) = U ^ 2 - 1 := by
      rw [mul_sub, mul_inv_cancel₀ hU, pow_two]
    have h' : U * (U - U⁻¹) = 0 := by rw [h, mul_zero]
    have h2 : U ^ 2 = 1 := sub_eq_zero.mp (by rw [hmul] at h'; exact h')
    exact sq_eq_one_iff.mp h2
  · rintro (rfl | rfl) <;> simp

/-- The zero at `U = 1` is simple: the cofactor `(U + 1)/U` equals `2` there. -/
theorem oddThetaReduction_factor_at_one (U : K) (hU : U ≠ 0) :
    U - U⁻¹ = (U - 1) * ((U + 1) / U) := by
  field_simp [hU]
  ring

/-- The zero at `U = -1` is simple: the cofactor `(U - 1)/U` equals `2` there. -/
theorem oddThetaReduction_factor_at_neg_one (U : K) (hU : U ≠ 0) :
    U - U⁻¹ = (U + 1) * ((U - 1) / U) := by
  field_simp [hU]
  ring

theorem oddThetaReduction_cofactor_at_one : ((1 : K) + 1) / 1 = 2 := by
  norm_num

theorem oddThetaReduction_cofactor_at_neg_one : ((-1 : K) - 1) / (-1) = 2 := by
  norm_num

/-- The pole at `U = 0` is simple: `U * (U - U^(-1))` extends to `U^2 - 1`,
whose value at zero is `-1`, so the pole order at zero is exactly one. -/
theorem oddThetaReduction_pole_at_zero (U : K) (hU : U ≠ 0) :
    U * (U - U⁻¹) = U ^ 2 - 1 := by
  field_simp [hU]

/-- The value at zero of the extension `U^2 - 1` of `U * (U - U^(-1))` is `-1`,
so the pole at zero has order exactly one. -/
theorem oddThetaReduction_pole_value :
    (fun U : K => U ^ 2 - 1) 0 = -1 := by
  simp

end FieldReduction

/-! ## 9. Summary -/

/-- **Summary of the theta unit, nonvanishing and q-adic divisor data.**
Every analytic carrier has a nonzero analytic theta value with one-sided
q-expansion `1 + 2 sum q^((n+1)^2)`, a positive real realisation, a
principal-unit decomposition `theta = 1 + q * u`, a formal q-expansion which is
a unit of order zero, an empty zero set on the q-disc, theta units and root
values compatible with `realThetaValue`, `qExpansionTerm` and the packet scales,
and the odd theta order-zero special-fibre reduction `U - U^(-1)` with simple
zeros at `±1` and a simple pole at `0`.  The source theta divisor, meromorphic
continuation and Kummer class are NOT proved. -/
theorem example36SourceThetaDivisor_summary :
    (∀ t : AnalyticThetaCarrier, analyticThetaValue t ≠ 0) ∧
    (∀ t : AnalyticThetaCarrier,
      analyticThetaValue t = 1 + (t.q : ℂ) * (thetaQAdicQuotient t : ℂ)) ∧
    (∀ t : AnalyticThetaCarrier, 0 < thetaRealValue t) ∧
    analyticThetaZeroSet = ∅ ∧
    IsUnit gaussianThetaFormalSeries ∧
    PowerSeries.order gaussianThetaFormalSeries = 0 ∧
    (∀ (t : AnalyticThetaCarrier) (j : ℤ),
      thetaUnit (analyticThetaTransport t) j = thetaUnit t j ^ 2) ∧
    (∀ (l : PrimeGeFive) (j : SignedLabel l.value),
      ((thetaUnit analyticThetaCarrierConcrete j.1 : ℝˣ) : ℝ) =
        (sourceTheater l).thetaPacket.scale j) ∧
    (∀ (j : ℤ),
      ((thetaRootValue (Real.sqrt gaussianFiveThetaQ) j ^ 2 : ℝ) : ℂ) =
        qExpansionTerm j) :=
  ⟨analyticThetaValue_ne_zero, analyticThetaValue_eq_one_add_q_mul,
    thetaRealValue_pos, analyticThetaZeroSet_empty, gaussianThetaFormalSeries_isUnit,
    gaussianThetaFormalSeries_order, thetaUnit_transport,
    thetaUnit_concrete_packetScale, thetaRootValue_sqrt_concrete_sq_complex⟩

end

end SourceThetaDivisor
end Example36
end Frobenioid
end IUTII
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the theta unit / q-adic divisor data at the Example 3.6
carrier.  Constructed: the analytic theta value on every carrier `0 < q < 1`
with one-sided Mathlib q-expansion, strict positivity and nonvanishing, the
principal-unit decomposition `theta = 1 + q * u` with explicit positive `u`,
the concrete identification with `jacobiThetaQ` at q = 1/5, the formal theta
q-expansion as a unit of `PowerSeries ℤ` with `order = 0`, the empty zero set on
the q-disc, theta units and root values with `mu_(2l)` orbit compatibility and
the concrete square root of `1/5`, and the odd theta order-zero special-fibre
reduction `U - U^(-1)` with simple zeros at `±1` and a simple pole at `0`.
NOT proved: the two-sided convergence of the odd theta series, the shift law and
odd-theta nonvanishing of EtTh Proposition 1.4 (ii), the meromorphic
continuation to the Tate curve and the divisor statement of Proposition 1.4 (i)
(zeros = cusps of multiplicity one, poles = D_1), and the Kummer-class /
line-bundle identification of Proposition 1.4 (iii).  In particular the empty
zero divisor of the even theta q-series is not the source theta divisor. -/
def example36SourceThetaDivisor : Obligation :=
  { id := "IUT-II.example36-source-theta-divisor"
    source :=
      "EtTh Proposition 1.4 (i), (ii), (iii); IUT II, theta evaluation and " ++
        "q-expansion; IUT I, Definition 3.6, Corollary 3.7"
    status := VerificationStatus.testCarrier
    note :=
      "Constructed the actual analytic theta value on every AnalyticThetaCarrier " ++
        "(0 < q < 1) via tau = i log(1/q)/pi with exp(pi i tau) = q.  Proved " ++
        "the one-sided q-expansion theta = 1 + 2 sum_{n>=0} q^((n+1)^2) " ++
        "(analyticThetaValue_eq_tsum_nat), its complexified real form " ++
        "(analyticThetaValue_eq_ofReal), strict positivity of the real theta " ++
        "series and nonvanishing of the analytic theta value at every carrier " ++
        "(analyticThetaValue_ne_zero), and the identification with Mathlib's " ++
        "jacobiThetaQ at q = 1/5.  Proved the principal-unit decomposition " ++
        "theta = 1 + q * u with u = thetaQAdicQuotient t > 0, i.e. q-adic " ++
        "valuation zero (analyticThetaValue_eq_one_add_q_mul, " ++
        "thetaQAdicQuotient_pos).  Proved the formal theta q-expansion " ++
        "gaussianThetaFormalSeries (coefficient = multiplicity of n^2) has " ++
        "constant coefficient 1, is a unit of PowerSeries Z and has order 0.  " ++
        "Proved the zero set of the analytic theta function on the carrier is " ++
        "empty (analyticThetaZeroSet_empty) and packaged the trivial divisor " ++
        "statement (analyticThetaDivisor_trivial).  Proved theta units, " ++
        "thetaUnit = q^(j^2), label-negation, power-orbit compatibility under " ++
        "q -> q^2, concrete packet-scale identification, root values " ++
        "thetaRootValue r j = r^(j^2) with 2l-th root and mu_(2l)-orbit " ++
        "compatibility, and the concrete square root of 1/5 matching " ++
        "qExpansionTerm.  Proved the odd theta order-zero special-fibre " ++
        "reduction U - U^(-1) from the actual oddThetaTerm, its simple zeros at " ++
        "U = +-1 and its simple pole at U = 0.  NOT constructed: two-sided " ++
        "convergence of the odd theta series, the shift law/nonvanishing of " ++
        "EtTh Prop 1.4 (ii), the meromorphic continuation and divisor of Prop " ++
        "1.4 (i) on the Tate curve (zeros precisely at the cusps with " ++
        "multiplicity one, pole divisor D_1), and the Kummer-class/line-bundle " ++
        "statement of Prop 1.4 (iii).  The trivial divisor of the even theta " ++
        "q-series does not imply the source theta divisor; no q-series " ++
        "coefficient comparison is claimed to establish it."
    dependsOn :=
      [ "IUT-II.example36-source-theta-generator",
        "IUT-II.example36-theta-series",
        "IUT-II.example36-source-theater-carrier",
        "Foundations.Theta.gaussian-kernel",
        "Foundations.Theta.odd-theta" ] }

end LeanFormal.IUT.Audit
