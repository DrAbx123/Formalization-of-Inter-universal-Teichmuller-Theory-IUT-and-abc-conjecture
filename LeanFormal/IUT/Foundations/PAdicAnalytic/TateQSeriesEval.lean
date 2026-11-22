/-
  Scratch bridge: actual p-adic evaluation of Tate q-series over Z_5.

  The formal q-series C4, C6, D, H live in PowerSeries (PadicInt 5)
  (see TateQSeriesCoefficients.lean).  This file defines the actual
  evaluation map

      eval f q = sum_n (coeff_n f : Q_5) * q^n

  as a p-adic tsum, proves that it is additive and multiplicative on all
  coefficient families over Z_5 when ||q|| < 1, and identifies the
  evaluations of the four formal series with the genuine q-series Weierstrass
  quantities c4(q), c6(q), Delta(q) and Delta(q)/c4(q)^3.

  No PowerSeries.eval2Hom, no sorry, no axiom, no card.
-/

import LeanFormal.IUT.Foundations.PAdicAnalytic.TateQSeriesCoefficients
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Inverse

open scoped BigOperators
open PowerSeries

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.PAdicAnalytic

noncomputable section

local instance fivePrimeFactEval : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-! ## The evaluation map and its summability -/

/-- Actual p-adic evaluation of a formal power series over Z_5:
eval f q = sum_n (coeff n f) * q^n, as a Q_5-valued tsum. -/
noncomputable def padicPowerSeriesEval
    (f : PowerSeries (PadicInt 5)) (q : ℚ_[5]) : ℚ_[5] :=
  ∑' n : ℕ, ((f.coeff n : PadicInt 5) : ℚ_[5]) * q ^ n

/-- Every coefficient of a power series over Z_5 has p-adic norm at most one. -/
lemma norm_coeff_padicPowerSeries_le_one
    (f : PowerSeries (PadicInt 5)) (n : ℕ) :
    ‖(((f.coeff n : PadicInt 5) : ℚ_[5]))‖ ≤ 1 := by
  simpa using PadicInt.norm_le_one (f.coeff n)

/-- For ||q|| < 1, the coefficient family of the evaluation of any
power series over Z_5 is summable: it is dominated by the geometric
series ||q||^n. -/
theorem summable_padicPowerSeriesEval
    (f : PowerSeries (PadicInt 5)) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ((f.coeff n : PadicInt 5) : ℚ_[5]) * q ^ n := by
  have hqR : ‖(‖q‖ : ℝ)‖ < 1 := by simpa using hq
  have hgeom : Summable fun n : ℕ => ‖q‖ ^ n :=
    summable_geometric_of_norm_lt_one hqR
  refine Summable.of_norm_bounded hgeom fun n => ?_
  rw [norm_mul, norm_pow]
  have hcoeff := norm_coeff_padicPowerSeries_le_one f n
  have hqpow : 0 ≤ ‖q‖ ^ n := pow_nonneg (norm_nonneg q) n
  calc
    ‖(((f.coeff n : PadicInt 5) : ℚ_[5]))‖ * ‖q‖ ^ n
        ≤ 1 * ‖q‖ ^ n := mul_le_mul_of_nonneg_right hcoeff hqpow
    _ = ‖q‖ ^ n := one_mul _

/-- Norm summability of the evaluation coefficient family. -/
theorem summable_norm_padicPowerSeriesEval
    (f : PowerSeries (PadicInt 5)) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖((f.coeff n : PadicInt 5) : ℚ_[5]) * q ^ n‖ := by
  have hqR : ‖(‖q‖ : ℝ)‖ < 1 := by simpa using hq
  have hgeom : Summable fun n : ℕ => ‖q‖ ^ n :=
    summable_geometric_of_norm_lt_one hqR
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeom
  have hcoeff := norm_coeff_padicPowerSeries_le_one f n
  have hqpow : 0 ≤ ‖q‖ ^ n := pow_nonneg (norm_nonneg q) n
  calc
    ‖(((f.coeff n : PadicInt 5) : ℚ_[5])) * q ^ n‖
        = ‖(((f.coeff n : PadicInt 5) : ℚ_[5]))‖ * ‖q‖ ^ n := by
          rw [norm_mul, norm_pow]
    _ ≤ 1 * ‖q‖ ^ n := mul_le_mul_of_nonneg_right hcoeff hqpow
    _ = ‖q‖ ^ n := one_mul _

/-! ## Additivity and the constant/coordinate series -/

@[simp]
theorem padicPowerSeriesEval_zero (q : ℚ_[5]) :
    padicPowerSeriesEval 0 q = 0 := by
  simp [padicPowerSeriesEval]

theorem padicPowerSeriesEval_add
    (f g : PowerSeries (PadicInt 5)) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicPowerSeriesEval (f + g) q =
      padicPowerSeriesEval f q + padicPowerSeriesEval g q := by
  unfold padicPowerSeriesEval
  simp only [map_add, PadicInt.coe_add, add_mul]
  rw [Summable.tsum_add (summable_padicPowerSeriesEval f hq)
    (summable_padicPowerSeriesEval g hq)]

theorem padicPowerSeriesEval_neg
    (f : PowerSeries (PadicInt 5)) (q : ℚ_[5]) :
    padicPowerSeriesEval (-f) q = -padicPowerSeriesEval f q := by
  unfold padicPowerSeriesEval
  simp only [map_neg, PadicInt.coe_neg, neg_mul]
  rw [tsum_neg]

theorem padicPowerSeriesEval_sub
    (f g : PowerSeries (PadicInt 5)) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicPowerSeriesEval (f - g) q =
      padicPowerSeriesEval f q - padicPowerSeriesEval g q := by
  rw [sub_eq_add_neg, padicPowerSeriesEval_add _ _ hq,
    padicPowerSeriesEval_neg]
  ring

@[simp]
theorem padicPowerSeriesEval_C (c : PadicInt 5) (q : ℚ_[5]) :
    padicPowerSeriesEval (PowerSeries.C c) q = (c : ℚ_[5]) := by
  unfold padicPowerSeriesEval
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [PowerSeries.coeff_C, hn]

@[simp]
theorem padicPowerSeriesEval_one (q : ℚ_[5]) :
    padicPowerSeriesEval (1 : PowerSeries (PadicInt 5)) q = 1 := by
  simpa using padicPowerSeriesEval_C (1 : PadicInt 5) q

@[simp]
theorem padicPowerSeriesEval_X (q : ℚ_[5]) :
    padicPowerSeriesEval (PowerSeries.X : PowerSeries (PadicInt 5)) q = q := by
  unfold padicPowerSeriesEval
  rw [tsum_eq_single 1]
  · simp
  · intro n hn
    simp [PowerSeries.coeff_X, hn]

theorem padicPowerSeriesEval_C_mul
    (c : PadicInt 5) (f : PowerSeries (PadicInt 5)) (q : ℚ_[5]) :
    padicPowerSeriesEval (PowerSeries.C c * f) q =
      (c : ℚ_[5]) * padicPowerSeriesEval f q := by
  unfold padicPowerSeriesEval
  simp only [PowerSeries.coeff_C_mul, PadicInt.coe_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

/-! ## Multiplicativity via the Cauchy product -/

/-- The p-adic evaluation map is multiplicative: the coefficient family of a
product is the Cauchy convolution, and the corresponding antidiagonal family
is summable because all coefficients lie in Z_5. -/
theorem padicPowerSeriesEval_mul
    (f g : PowerSeries (PadicInt 5)) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicPowerSeriesEval (f * g) q =
      padicPowerSeriesEval f q * padicPowerSeriesEval g q := by
  let ef : ℕ → ℚ_[5] :=
    fun n => ((f.coeff n : PadicInt 5) : ℚ_[5]) * q ^ n
  let eg : ℕ → ℚ_[5] :=
    fun n => ((g.coeff n : PadicInt 5) : ℚ_[5]) * q ^ n
  have hfn : Summable fun n : ℕ => ‖ef n‖ :=
    summable_norm_padicPowerSeriesEval f hq
  have hgn : Summable fun n : ℕ => ‖eg n‖ :=
    summable_norm_padicPowerSeriesEval g hq
  have hanti :
      padicPowerSeriesEval f q * padicPowerSeriesEval g q =
        ∑' n : ℕ, ∑ kl ∈ Finset.antidiagonal n, ef kl.1 * eg kl.2 := by
    change (∑' n : ℕ, ef n) * (∑' n : ℕ, eg n) = _
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn]
  calc
    padicPowerSeriesEval (f * g) q
        = ∑' n : ℕ, ((f * g).coeff n : ℚ_[5]) * q ^ n := rfl
    _ = ∑' n : ℕ, ∑ kl ∈ Finset.antidiagonal n, ef kl.1 * eg kl.2 := by
          apply tsum_congr
          intro n
          rw [PowerSeries.coeff_mul]
          simp only [PadicInt.coe_sum]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro kl hkl
          have hkl' : kl.1 + kl.2 = n := by
            simpa using (Finset.mem_antidiagonal.mp hkl)
          simp only [ef, eg, PadicInt.coe_mul]
          rw [← hkl', pow_add]
          ring
    _ = padicPowerSeriesEval f q * padicPowerSeriesEval g q := hanti.symm

/-- Powers evaluate to powers. -/
theorem padicPowerSeriesEval_pow
    (f : PowerSeries (PadicInt 5)) (n : ℕ) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicPowerSeriesEval (f ^ n) q = padicPowerSeriesEval f q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, padicPowerSeriesEval_mul _ _ hq, ih, pow_succ]

/-! ## The Lambert coefficient identity in evaluation form -/

/-- Convert a natural-indexed sum whose zeroth term vanishes into a positive-indexed sum. -/
lemma tsum_nat_eq_tsum_pnat_of_zero
    (f : ℕ → ℚ_[5]) (hf : Summable f) (h0 : f 0 = 0) :
    (∑' n : ℕ, f n) = ∑' n : ℕ+, f n := by
  rw [hf.tsum_eq_zero_add, h0, zero_add, ← tsum_pnat_eq_tsum_succ (f := f)]

/-- The actual Lambert coefficient identity gives the evaluation of the formal
Lambert series tateS_k as the genuine p-adic Lambert series S_k(q). -/
theorem padicPowerSeriesEval_lambertFormal
    (k : ℕ) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicPowerSeriesEval (PowerSeries.mk (lambertCoeffZ k)) q =
      lambertCoefficientSeries k q := by
  have hcoeff : ∀ n : ℕ,
      (((PowerSeries.mk (lambertCoeffZ k)).coeff n : PadicInt 5) : ℚ_[5]) =
        (ArithmeticFunction.sigma k n : ℚ_[5]) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [lambertCoeffZ]
    · simp [lambertCoeffZ, hn]
  have hsum : (∑' n : ℕ,
        (((PowerSeries.mk (lambertCoeffZ k)).coeff n : PadicInt 5) : ℚ_[5]) * q ^ n) =
      ∑' n : ℕ, (ArithmeticFunction.sigma k n : ℚ_[5]) * q ^ n := by
    apply tsum_congr
    intro n
    rw [hcoeff n]
  have hsumm : Summable fun n : ℕ =>
      (ArithmeticFunction.sigma k n : ℚ_[5]) * q ^ n := by
    refine (summable_padicPowerSeriesEval (PowerSeries.mk (lambertCoeffZ k)) hq).congr ?_
    intro n
    rw [hcoeff n]
  have h0 : (fun n : ℕ => (ArithmeticFunction.sigma k n : ℚ_[5]) * q ^ n) 0 = 0 := by
    simp
  rw [padicPowerSeriesEval, hsum, tsum_nat_eq_tsum_pnat_of_zero _ hsumm h0,
    ← lambertCoefficientSeries_eq_tsum_sigma k hq]

theorem padicPowerSeriesEval_tateS3Formal {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicPowerSeriesEval tateS3Formal q = lambertCoefficientSeries 3 q := by
  simpa [tateS3Formal] using padicPowerSeriesEval_lambertFormal 3 hq

theorem padicPowerSeriesEval_tateS5Formal {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicPowerSeriesEval tateS5Formal q = lambertCoefficientSeries 5 q := by
  simpa [tateS5Formal] using padicPowerSeriesEval_lambertFormal 5 hq

/-! ## Evaluation of C4, C6, D, H -/

/-- Evaluation of the formal C4 is the classical expression 1 + 240 * S_3(q). -/
theorem padicPowerSeriesEval_tateC4Formal_eq_lambert
    {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicPowerSeriesEval tateC4Formal q =
      1 + 240 * lambertCoefficientSeries 3 q := by
  rw [tateC4Formal, padicPowerSeriesEval_add _ _ hq,
    padicPowerSeriesEval_one, padicPowerSeriesEval_C_mul,
    padicPowerSeriesEval_tateS3Formal hq]
  change 1 + (240 : ℚ_[5]) * lambertCoefficientSeries 3 q =
    1 + 240 * lambertCoefficientSeries 3 q
  ring

/-- Evaluation of the formal C4 is the genuine Weierstrass c4(q) of the
canonical Tate equation. -/
theorem padicPowerSeriesEval_tateC4Formal
    {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicPowerSeriesEval tateC4Formal q =
      (TateCurve.weierstrassCurve ℚ_[5] q).c₄ := by
  rw [padicPowerSeriesEval_tateC4Formal_eq_lambert hq,
    TateCurve.canonical_c₄, TateCurve.a4, lambertCoefficientSeries]
  ring

/-- Evaluation of the formal C6 is the classical expression -1 + 504 * S_5(q). -/
theorem padicPowerSeriesEval_tateC6Formal_eq_lambert
    {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicPowerSeriesEval tateC6Formal q =
      -1 + 504 * lambertCoefficientSeries 5 q := by
  rw [tateC6Formal,
    show (-1 : PowerSeries (PadicInt 5)) = PowerSeries.C (-1) by simp,
    padicPowerSeriesEval_add _ _ hq, padicPowerSeriesEval_C,
    padicPowerSeriesEval_C_mul, padicPowerSeriesEval_tateS5Formal hq]
  change (-1 : ℚ_[5]) + (504 : ℚ_[5]) * lambertCoefficientSeries 5 q =
    -1 + 504 * lambertCoefficientSeries 5 q
  ring

/-- Evaluation of the formal C6 is the genuine Weierstrass c6(q) of the
canonical Tate equation. -/
theorem padicPowerSeriesEval_tateC6Formal
    {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicPowerSeriesEval tateC6Formal q =
      (TateCurve.weierstrassCurve ℚ_[5] q).c₆ := by
  rw [padicPowerSeriesEval_tateC6Formal_eq_lambert hq,
    TateCurve.canonical_c₆, TateCurve.a4, TateCurve.a6,
    lambertCoefficientSeries]
  ring

/-- Evaluation of the numerator C4^3 - C6^2 is c4(q)^3 - c6(q)^2. -/
theorem padicPowerSeriesEval_tateDFormalNumerator
    {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicPowerSeriesEval tateDFormalNumerator q =
      (TateCurve.weierstrassCurve ℚ_[5] q).c₄ ^ 3 -
        (TateCurve.weierstrassCurve ℚ_[5] q).c₆ ^ 2 := by
  rw [tateDFormalNumerator, padicPowerSeriesEval_sub _ _ hq,
    padicPowerSeriesEval_pow _ 3 hq, padicPowerSeriesEval_pow _ 2 hq,
    padicPowerSeriesEval_tateC4Formal hq,
    padicPowerSeriesEval_tateC6Formal hq]

/-- Evaluation of the normalized formal discriminant D = (C4^3 - C6^2)/1728
is the genuine Weierstrass discriminant Delta(q). -/
theorem padicPowerSeriesEval_tateDFormal
    {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicPowerSeriesEval tateDFormal q =
      (TateCurve.weierstrassCurve ℚ_[5] q).Δ := by
  have hmul : (1728 : PadicInt 5) * (↑(unit1728⁻¹) : PadicInt 5) = 1 := by
    rw [← val_unit1728]
    simp
  have hu : (1728 : ℚ_[5]) * ((↑(unit1728⁻¹) : PadicInt 5) : ℚ_[5]) = 1 := by
    have hcast := congrArg (fun z : PadicInt 5 => (z : ℚ_[5])) hmul
    rw [PadicInt.coe_mul, PadicInt.coe_one] at hcast
    exact hcast
  rw [tateDFormal, padicPowerSeriesEval_mul _ _ hq,
    padicPowerSeriesEval_tateDFormalNumerator hq, padicPowerSeriesEval_C,
    ← TateCurve.canonical_c_relation]
  calc
    (1728 * (TateCurve.weierstrassCurve ℚ_[5] q).Δ) *
        ((↑(unit1728⁻¹) : PadicInt 5) : ℚ_[5])
        = (TateCurve.weierstrassCurve ℚ_[5] q).Δ *
            ((1728 : ℚ_[5]) * ((↑(unit1728⁻¹) : PadicInt 5) : ℚ_[5])) := by
          ring
    _ = (TateCurve.weierstrassCurve ℚ_[5] q).Δ * 1 := by rw [hu]
    _ = (TateCurve.weierstrassCurve ℚ_[5] q).Δ := by ring

/-- Evaluation sends a formal inverse invOfUnit f 1 to the field inverse
of eval f, via the formal identity f * invOfUnit f 1 = 1 and multiplicativity. -/
theorem padicPowerSeriesEval_invOfUnit
    (f : PowerSeries (PadicInt 5))
    (hf : PowerSeries.constantCoeff f = 1) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicPowerSeriesEval (PowerSeries.invOfUnit f 1) q =
      (padicPowerSeriesEval f q)⁻¹ := by
  have h := congrArg
    (fun s : PowerSeries (PadicInt 5) => padicPowerSeriesEval s q)
    (PowerSeries.mul_invOfUnit f 1 hf)
  simp only [padicPowerSeriesEval_mul _ _ hq, padicPowerSeriesEval_one] at h
  exact eq_inv_of_mul_eq_one_right h

/-- Evaluation of the formal H = D / C4^3 is the genuine expression
Delta(q) / c4(q)^3. -/
theorem padicPowerSeriesEval_tateHFormal
    {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicPowerSeriesEval tateHFormal q =
      (TateCurve.weierstrassCurve ℚ_[5] q).Δ /
        (TateCurve.weierstrassCurve ℚ_[5] q).c₄ ^ 3 := by
  have hc : PowerSeries.constantCoeff (tateC4Formal ^ 3) = 1 := by
    rw [map_pow, constantCoeff_tateC4Formal, one_pow]
  rw [tateHFormal, padicPowerSeriesEval_mul _ _ hq,
    padicPowerSeriesEval_tateDFormal hq,
    padicPowerSeriesEval_invOfUnit _ hc hq,
    padicPowerSeriesEval_pow _ 3 hq,
    padicPowerSeriesEval_tateC4Formal hq]
  rfl

end

end LeanFormal.IUT.PAdicAnalytic
