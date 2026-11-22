/-
  # Tate q-series coefficients: Lambert/divisor reindex

  Task-137, part (1).  The full coefficient identity needs the p-adic
  double-sum reindex

      sum_{n>=1} sum_{r>=1} n^k q^(n r) = sum_{m>=1} sigma_k(m) q^m.

  This file proves the actual pointwise geometric identity
  q^n/(1-q^n) = sum_{r>=1} (q^n)^r for |q|<1, so the Lambert series is
  identified with the double tsum over n>=1, r>=1.  The remaining reindex by
  the antidiagonal m = n*r is proved below for Q_5, replacing Mathlib's
  NormSMulClass-based proof by the p-adic antidiagonal summability argument.

  Mathlib's tsum_pow_div_one_sub_eq_tsum_sigma cannot be used directly for Q_5:
  it requires NormSMulClass Int Q_5, which is false for the p-adic norm
  (||5 : Q_5|| = 1/5 but ||5 : Int|| = 5).  The p-adic proof has to bound
  ||n^k|| by 1 and use the nonarchimedean majorant |q|^(n+r-1) for the double
  family.  That reindex is proved below for Q_5.
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.NumberTheory.Padics.PadicNumbers
import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic
import LeanFormal.IUT.Foundations.PAdicAnalytic.DivisorsAntidiagonalCard

open scoped ArithmeticFunction.sigma
open ArithmeticFunction

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.PAdicAnalytic

noncomputable section

local instance fivePrimeFactCoeff : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The Lambert coefficient function S_k on Q_5. -/
noncomputable def lambertCoefficientSeries (k : ℕ) (q : ℚ_[5]) : ℚ_[5] :=
  TateCurve.lambertSeries ℚ_[5] k q

/-- Pointwise geometric identity: for |q| < 1 and n >= 1,
q^n/(1-q^n) = sum_{r>=1} (q^n)^r. -/
theorem q_pow_div_one_sub_eq_tsum_pnat_geom
    {q : ℚ_[5]} (hq : ‖q‖ < 1) (n : ℕ+) :
    q ^ (n : ℕ) / (1 - q ^ (n : ℕ)) =
      ∑' r : ℕ+, (q ^ (n : ℕ)) ^ (r : ℕ) := by
  have hx : ‖q ^ (n : ℕ)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (PNat.ne_zero n)
  rw [tsum_pnat_eq_tsum_succ (f := fun r : ℕ => (q ^ (n : ℕ)) ^ r)]
  rw [show (∑' r : ℕ, (q ^ (n : ℕ)) ^ (r + 1)) =
      (q ^ (n : ℕ)) * ∑' r : ℕ, (q ^ (n : ℕ)) ^ r by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro r
    rw [pow_succ']]
  rw [tsum_geometric_of_norm_lt_one hx]
  field_simp

/-- The Lambert series as the actual p-adic double tsum over n>=1, r>=1. -/
theorem lambertCoefficientSeries_eq_double_tsum
    (k : ℕ) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    lambertCoefficientSeries k q =
      ∑' n : ℕ+,
        (n : ℚ_[5]) ^ k * ∑' r : ℕ+, q ^ ((n : ℕ) * (r : ℕ)) := by
  unfold lambertCoefficientSeries TateCurve.lambertSeries
  let f : ℕ → ℚ_[5] := fun n =>
    (n : ℚ_[5]) ^ k * q ^ n / (1 - q ^ n)
  have hs : Summable f := TateCurve.lambertSeries_summable ℚ_[5] k hq
  have hf0 : f 0 = 0 := by simp [f]
  change (∑' n : ℕ, f n) = _
  rw [hs.tsum_eq_zero_add, hf0, zero_add]
  rw [← tsum_pnat_eq_tsum_succ (f := f)]
  apply tsum_congr
  intro n
  change ((n : ℚ_[5]) ^ k * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))) =
    (n : ℚ_[5]) ^ k * ∑' r : ℕ+, q ^ ((n : ℕ) * (r : ℕ))
  have hgeom := q_pow_div_one_sub_eq_tsum_pnat_geom (q := q) hq n
  calc
    ((n : ℚ_[5])) ^ k * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))
        = (n : ℚ_[5]) ^ k * (q ^ (n : ℕ) / (1 - q ^ (n : ℕ))) := by ring
    _ = (n : ℚ_[5]) ^ k * ∑' r : ℕ+, (q ^ (n : ℕ)) ^ (r : ℕ) := by rw [hgeom]
    _ = (n : ℚ_[5]) ^ k * ∑' r : ℕ+, q ^ ((n : ℕ) * (r : ℕ)) := by
        congr 1
        apply tsum_congr
        intro r
        rw [pow_mul]



/-! ## P-adic antidiagonal summability and reindex -/

open Filter Nat Topology

/-- The p-adic norm of a natural number coerced into Q_5 is at most one. -/
lemma norm_natCast_le_one_padic (n : ℕ) : ‖(n : ℚ_[5])‖ ≤ 1 := by
  simpa using Padic.norm_int_le_one (p := 5) (n : ℤ)

/-- Summability of the p-adic antidiagonal family. -/
theorem summable_antidiagonal_padic
    (k : ℕ) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    Summable fun c : (n : ℕ+) × {x // x ∈ (n : ℕ).divisorsAntidiagonal} ↦
      (c.2.1.2 : ℚ_[5]) ^ k * q ^ (c.2.1.1 * c.2.1.2) := by
  have hbaseNat : Summable fun n : ℕ => (n : ℝ) * ‖q‖ ^ n := by
    simpa [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (k := 1) (r := ‖q‖)
        (by simpa using hq))
  have hbaseP : Summable fun n : ℕ+ => (n : ℝ) * ‖q‖ ^ (n : ℕ) :=
    hbaseNat.comp_injective (fun a b h => PNat.coe_injective h)
  have hg : Summable fun c : (n : ℕ+) × {x // x ∈ (n : ℕ).divisorsAntidiagonal} ↦
      ‖q‖ ^ (c.1 : ℕ) := by
    refine (summable_sigma_of_nonneg (fun c => pow_nonneg (norm_nonneg q) _)).mpr ?_
    constructor
    · intro n
      exact (hasSum_fintype _).summable
    · change Summable (fun n : ℕ+ =>
          ∑' y : {x // x ∈ (n : ℕ).divisorsAntidiagonal}, ‖q‖ ^ (n : ℕ))
      refine Summable.of_nonneg_of_le
        (f := fun n : ℕ+ => (n : ℝ) * ‖q‖ ^ (n : ℕ))
        (g := fun n : ℕ+ =>
          ∑' y : {x // x ∈ (n : ℕ).divisorsAntidiagonal}, ‖q‖ ^ (n : ℕ))
        (fun n => ?_) (fun n => ?_) hbaseP
      · exact tsum_nonneg (fun y => pow_nonneg (norm_nonneg q) _)
      · rw [tsum_fintype]
        have hcard : (Nat.divisorsAntidiagonal (n : ℕ)).card ≤ (n : ℕ) :=
          Nat.card_divisorsAntidiagonal_le (n : ℕ)
        simpa [Finset.sum_const, nsmul_eq_mul] using
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard)
            (pow_nonneg (norm_nonneg q) _)
  refine Summable.of_norm_bounded hg (fun c => ?_)
  have hprod : c.2.1.1 * c.2.1.2 = (c.1 : ℕ) :=
    (Nat.mem_divisorsAntidiagonal.mp c.2.2).1
  rw [norm_mul, norm_pow, hprod]
  have hx : ‖(c.2.1.2 : ℚ_[5])‖ ≤ 1 := norm_natCast_le_one_padic _
  have hqle : ‖q‖ ≤ 1 := hq.le
  have hqnonneg : 0 ≤ ‖q‖ := norm_nonneg q
  calc
    ‖(c.2.1.2 : ℚ_[5])‖ ^ k * ‖q ^ (c.1 : ℕ)‖
        = ‖(c.2.1.2 : ℚ_[5])‖ ^ k * ‖q‖ ^ (c.1 : ℕ) := by
          rw [norm_pow]
    _ ≤ 1 ^ k * ‖q‖ ^ (c.1 : ℕ) := by
          exact mul_le_mul_of_nonneg_right
            (by simpa using pow_le_one₀ (norm_nonneg _) hx)
            (pow_nonneg hqnonneg _)
    _ = ‖q‖ ^ (c.1 : ℕ) := by simp

/-- P-adic product form of the antidiagonal summability. -/
theorem summable_prod_mul_pow_padic
    (k : ℕ) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    Summable fun c : (ℕ+ × ℕ+) ↦
      (c.2 : ℚ_[5]) ^ k * q ^ (c.1 * c.2 : ℕ) := by
  have h := summable_antidiagonal_padic k hq
  refine (sigmaAntidiagonalEquivProd.summable_iff
    (f := fun c : ℕ+ × ℕ+ => (c.2 : ℚ_[5]) ^ k * q ^ (c.1 * c.2 : ℕ))).mp ?_
  convert h using 1
  ext c
  simp [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors]

/-- P-adic analogue of Mathlib's tsum_prod_pow_eq_tsum_sigma. -/
theorem tsum_prod_pow_eq_tsum_sigma_padic
    (k : ℕ) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    ∑' d : ℕ+, ∑' c : ℕ+, (c : ℚ_[5]) ^ k * q ^ (d * c : ℕ) =
      ∑' e : ℕ+, (σ k e : ℚ_[5]) * q ^ (e : ℕ) := by
  suffices ∑' c : ℕ+ × ℕ+, (c.2 : ℚ_[5]) ^ k * q ^ (c.1 * c.2 : ℕ) =
      ∑' e : ℕ+, (σ k e : ℚ_[5]) * q ^ (e : ℕ) by
    rwa [← (summable_prod_mul_pow_padic k hq).tsum_prod]
  simp only [← sigmaAntidiagonalEquivProd.tsum_eq, sigmaAntidiagonalEquivProd,
    divisorsAntidiagonalFactors, PNat.mk_coe, Equiv.coe_fn_mk, sigma_eq_sum_div, cast_sum,
    cast_pow, Summable.tsum_sigma (summable_antidiagonal_padic k hq :)]
  refine tsum_congr fun n ↦ ?_
  simpa [tsum_fintype, Finset.sum_mul,
    (n : ℕ).divisorsAntidiagonal.sum_attach (fun x : ℕ × ℕ ↦ (x.2 : ℚ_[5]) ^ k * q ^ (x.1 * x.2)),
    sum_divisorsAntidiagonal (fun x y ↦ (y : ℚ_[5]) ^ k * q ^ (x * y))]
      using Finset.sum_congr rfl fun i hi ↦ by rw [Nat.mul_div_cancel' (dvd_of_mem_divisors hi)]

/-- P-adic Lambert/divisor identity for arbitrary weight k. -/
theorem tsum_pow_div_one_sub_eq_tsum_sigma_padic
    (k : ℕ) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    ∑' n : ℕ+, (n : ℚ_[5]) ^ k * q ^ (n : ℕ) / (1 - q ^ (n : ℕ)) =
      ∑' n : ℕ+, (σ k n : ℚ_[5]) * q ^ (n : ℕ) := by
  have hgeomPN (m : ℕ+) :
      ∑' r : ℕ+, (q ^ (m : ℕ)) ^ (r : ℕ) = (1 - q ^ (m : ℕ))⁻¹ - 1 := by
    have hqpow : ‖q ^ (m : ℕ)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq (PNat.ne_zero m)
    have hxne : (1 : ℚ_[5]) - q ^ (m : ℕ) ≠ 0 := by
      intro h
      have hqeq : q ^ (m : ℕ) = 1 := by
        have := sub_eq_zero.mp h
        exact this.symm
      have hnorm : ‖q ^ (m : ℕ)‖ = 1 := by rw [hqeq]; simp
      exact (ne_of_lt hqpow) hnorm
    rw [tsum_pnat_eq_tsum_succ (f := fun r : ℕ => (q ^ (m : ℕ)) ^ r)]
    calc
      (∑' r : ℕ, (q ^ (m : ℕ)) ^ (r + 1)) =
          (q ^ (m : ℕ)) * ∑' r : ℕ, (q ^ (m : ℕ)) ^ r := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro r
        rw [_root_.pow_succ']
      _ = (q ^ (m : ℕ)) * (1 - q ^ (m : ℕ))⁻¹ := by
        rw [tsum_geometric_of_norm_lt_one hqpow]
      _ = (1 - q ^ (m : ℕ))⁻¹ - 1 := by
        field_simp [hxne]
        ring
  simp only [div_eq_mul_inv]
  calc
    ∑' n : ℕ+, (n : ℚ_[5]) ^ k * q ^ (n : ℕ) * (1 - q ^ (n : ℕ))⁻¹ =
        ∑' n : ℕ+, (n : ℚ_[5]) ^ k * ((1 - q ^ (n : ℕ))⁻¹) * q ^ (n : ℕ) := by
      apply tsum_congr
      intro n
      ring
    _ = ∑' n : ℕ+, (n : ℚ_[5]) ^ k * (∑' r : ℕ+, q ^ ((n : ℕ) * (r : ℕ))) := by
      apply tsum_congr
      intro n
      have h := hgeomPN n
      rw [show (∑' r : ℕ+, q ^ ((n : ℕ) * (r : ℕ))) =
          (1 - q ^ (n : ℕ))⁻¹ - 1 by
        simpa [pow_mul] using h]
      have hnne : (1 : ℚ_[5]) - q ^ (n : ℕ) ≠ 0 := by
        intro hz
        have hqeq : q ^ (n : ℕ) = 1 := by
          have := sub_eq_zero.mp hz
          exact this.symm
        have hnorm : ‖q ^ (n : ℕ)‖ = 1 := by rw [hqeq]; simp
        have hqpow : ‖q ^ (n : ℕ)‖ < 1 := by
          rw [norm_pow]
          exact pow_lt_one₀ (norm_nonneg q) hq (PNat.ne_zero n)
        exact (ne_of_lt hqpow) hnorm
      field_simp [hnne]
      ring
    _ = ∑' d : ℕ+, ∑' c : ℕ+, (c : ℚ_[5]) ^ k * q ^ (d * c : ℕ) := by
      rw [show (∑' n : ℕ+, (n : ℚ_[5]) ^ k *
            (∑' r : ℕ+, q ^ ((n : ℕ) * (r : ℕ)))) =
          ∑' n : ℕ+, ∑' r : ℕ+, (n : ℚ_[5]) ^ k * q ^ ((n : ℕ) * (r : ℕ)) by
        apply tsum_congr
        intro n
        rw [tsum_mul_left]]
      have hs : Summable (Function.uncurry fun n r : ℕ+ =>
          (n : ℚ_[5]) ^ k * q ^ ((n : ℕ) * (r : ℕ))) := by
        change Summable (fun p : ℕ+ × ℕ+ =>
          (p.1 : ℚ_[5]) ^ k * q ^ ((p.1 : ℕ) * (p.2 : ℕ)))
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (summable_prod_mul_pow_padic k hq).prod_symm
      calc
        (∑' n : ℕ+, ∑' r : ℕ+,
            (n : ℚ_[5]) ^ k * q ^ ((n : ℕ) * (r : ℕ))) =
          ∑' r : ℕ+, ∑' n : ℕ+,
            (n : ℚ_[5]) ^ k * q ^ ((n : ℕ) * (r : ℕ)) := hs.tsum_comm.symm
        _ = ∑' d : ℕ+, ∑' c : ℕ+, (c : ℚ_[5]) ^ k * q ^ (d * c : ℕ) := by
          apply tsum_congr
          intro d
          apply tsum_congr
          intro c
          rw [mul_comm (c : ℕ) (d : ℕ)]
    _ = ∑' n : ℕ+, (σ k n : ℚ_[5]) * q ^ (n : ℕ) :=
      tsum_prod_pow_eq_tsum_sigma_padic k hq

/-- Actual Lambert coefficient identity: the Tate Lambert series S_k equals the
divisor-sum q-series. -/
theorem lambertCoefficientSeries_eq_tsum_sigma
    (k : ℕ) {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    lambertCoefficientSeries k q =
      ∑' m : ℕ+, (σ k m : ℚ_[5]) * q ^ (m : ℕ) := by
  let f : ℕ → ℚ_[5] := fun n => (n : ℚ_[5]) ^ k * q ^ n / (1 - q ^ n)
  have hs : Summable f := TateCurve.lambertSeries_summable ℚ_[5] k hq
  have hf0 : f 0 = 0 := by simp [f]
  change (∑' n : ℕ, f n) = _
  rw [hs.tsum_eq_zero_add, hf0, zero_add]
  rw [← tsum_pnat_eq_tsum_succ (f := f)]
  simpa [f] using tsum_pow_div_one_sub_eq_tsum_sigma_padic k hq

noncomputable def lambertCoeffZ (k n : ℕ) : PadicInt 5 :=
  if n = 0 then 0 else (σ k n : PadicInt 5)

noncomputable def tateS3Formal : PowerSeries (PadicInt 5) := PowerSeries.mk (lambertCoeffZ 3)
noncomputable def tateS5Formal : PowerSeries (PadicInt 5) := PowerSeries.mk (lambertCoeffZ 5)
noncomputable def tateC4Formal : PowerSeries (PadicInt 5) := 1 + PowerSeries.C (240 : PadicInt 5) * tateS3Formal
noncomputable def tateC6Formal : PowerSeries (PadicInt 5) := -1 + PowerSeries.C (504 : PadicInt 5) * tateS5Formal
noncomputable def tateDFormalNumerator : PowerSeries (PadicInt 5) :=
  tateC4Formal ^ 3 - tateC6Formal ^ 2

@[simp] theorem coeff_lambertCoeffZ_zero (k : ℕ) : lambertCoeffZ k 0 = 0 := by simp [lambertCoeffZ]

@[simp] theorem coeff_tateS3Formal_zero : PowerSeries.coeff 0 tateS3Formal = 0 := by
  simp [tateS3Formal]

@[simp] theorem coeff_tateS5Formal_zero : PowerSeries.coeff 0 tateS5Formal = 0 := by
  simp [tateS5Formal]

theorem coeff_tateS3Formal_one : PowerSeries.coeff 1 tateS3Formal = 1 := by
  simp [tateS3Formal, lambertCoeffZ, ArithmeticFunction.sigma_apply]

theorem coeff_tateS5Formal_one : PowerSeries.coeff 1 tateS5Formal = 1 := by
  simp [tateS5Formal, lambertCoeffZ, ArithmeticFunction.sigma_apply]

@[simp] theorem constantCoeff_tateC4Formal : PowerSeries.constantCoeff tateC4Formal = 1 := by
  simp [tateC4Formal, tateS3Formal, lambertCoeffZ]

@[simp] theorem constantCoeff_tateC6Formal : PowerSeries.constantCoeff tateC6Formal = -1 := by
  simp [tateC6Formal, tateS5Formal, lambertCoeffZ]

@[simp] theorem coeff_tateC4Formal_zero : PowerSeries.coeff 0 tateC4Formal = 1 := by
  simp [tateC4Formal, tateS3Formal, lambertCoeffZ]

theorem coeff_tateC4Formal_one : PowerSeries.coeff 1 tateC4Formal = 240 := by
  simp [tateC4Formal, tateS3Formal, lambertCoeffZ, ArithmeticFunction.sigma_apply]

@[simp] theorem coeff_tateC6Formal_zero : PowerSeries.coeff 0 tateC6Formal = -1 := by
  simp [tateC6Formal, tateS5Formal, lambertCoeffZ]

theorem coeff_tateC6Formal_one : PowerSeries.coeff 1 tateC6Formal = 504 := by
  simp [tateC6Formal, tateS5Formal, lambertCoeffZ, ArithmeticFunction.sigma_apply]


lemma coeff_zero_mul_powerSeries (f g : PowerSeries (PadicInt 5)) :
    PowerSeries.coeff 0 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 0 g := by
  rw [PowerSeries.coeff_mul]
  simp [Finset.Nat.antidiagonal_zero]

lemma coeff_one_mul_powerSeries (f g : PowerSeries (PadicInt 5)) :
    PowerSeries.coeff 1 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.antidiagonal_succ]
  simp [Finset.Nat.antidiagonal_zero, add_comm, add_left_comm, add_assoc]

theorem coeff_tateC4Formal_sq_zero : PowerSeries.coeff 0 (tateC4Formal ^ 2) = 1 := by
  rw [pow_two, coeff_zero_mul_powerSeries, coeff_tateC4Formal_zero]
  ring

theorem coeff_tateC4Formal_sq_one : PowerSeries.coeff 1 (tateC4Formal ^ 2) = 480 := by
  rw [pow_two, coeff_one_mul_powerSeries, coeff_tateC4Formal_zero,
    coeff_tateC4Formal_one]
  ring

theorem coeff_tateC4Formal_cube_zero : PowerSeries.coeff 0 (tateC4Formal ^ 3) = 1 := by
  rw [show tateC4Formal ^ 3 = tateC4Formal ^ 2 * tateC4Formal by ring]
  rw [coeff_zero_mul_powerSeries, coeff_tateC4Formal_sq_zero, coeff_tateC4Formal_zero]
  ring

theorem coeff_tateC4Formal_cube_one : PowerSeries.coeff 1 (tateC4Formal ^ 3) = 720 := by
  rw [show tateC4Formal ^ 3 = tateC4Formal ^ 2 * tateC4Formal by ring]
  rw [coeff_one_mul_powerSeries, coeff_tateC4Formal_sq_zero,
    coeff_tateC4Formal_sq_one, coeff_tateC4Formal_zero, coeff_tateC4Formal_one]
  ring

theorem coeff_tateC6Formal_sq_zero : PowerSeries.coeff 0 (tateC6Formal ^ 2) = 1 := by
  rw [pow_two, coeff_zero_mul_powerSeries, coeff_tateC6Formal_zero]
  ring

theorem coeff_tateC6Formal_sq_one : PowerSeries.coeff 1 (tateC6Formal ^ 2) = -1008 := by
  rw [pow_two, coeff_one_mul_powerSeries, coeff_tateC6Formal_zero,
    coeff_tateC6Formal_one]
  ring

theorem coeff_tateDFormalNumerator_zero :
    PowerSeries.coeff 0 tateDFormalNumerator = 0 := by
  simp [tateDFormalNumerator, coeff_tateC4Formal_cube_zero,
    coeff_tateC6Formal_sq_zero]

theorem coeff_tateDFormalNumerator_one :
    PowerSeries.coeff 1 tateDFormalNumerator = 1728 := by
  simp [tateDFormalNumerator, coeff_tateC4Formal_cube_one,
    coeff_tateC6Formal_sq_one]
  norm_num

lemma isUnit_1728_padicInt : IsUnit (1728 : PadicInt 5) := by
  rw [PadicInt.isUnit_iff]
  change ‖((1728 : ℕ) : PadicInt 5)‖ = 1
  rw [PadicInt.norm_natCast_eq_one_iff]
  decide

noncomputable def unit1728 : (PadicInt 5)ˣ := isUnit_1728_padicInt.unit

theorem val_unit1728 : (unit1728 : PadicInt 5) = 1728 :=
  isUnit_1728_padicInt.unit_spec

noncomputable def tateDFormal : PowerSeries (PadicInt 5) :=
  tateDFormalNumerator * PowerSeries.C (↑(unit1728⁻¹) : PadicInt 5)

theorem coeff_tateDFormal_zero : PowerSeries.coeff 0 tateDFormal = 0 := by
  rw [tateDFormal, coeff_zero_mul_powerSeries, coeff_tateDFormalNumerator_zero]
  ring

theorem coeff_tateDFormal_one : PowerSeries.coeff 1 tateDFormal = 1 := by
  rw [tateDFormal, coeff_one_mul_powerSeries, coeff_tateDFormalNumerator_zero,
    coeff_tateDFormalNumerator_one]
  have hC0 : PowerSeries.coeff 0 (PowerSeries.C (↑(unit1728⁻¹) : PadicInt 5)) =
      (↑(unit1728⁻¹) : PadicInt 5) := by simp
  have hC1 : PowerSeries.coeff 1 (PowerSeries.C (↑(unit1728⁻¹) : PadicInt 5)) = 0 := by simp
  rw [hC0, hC1]
  have hmul : (1728 : PadicInt 5) * (↑(unit1728⁻¹) : PadicInt 5) = 1 := by
    rw [← val_unit1728]
    simpa using congrArg (fun u : (PadicInt 5)ˣ => (u : PadicInt 5))
      (Units.mul_inv unit1728)
  simpa using hmul



theorem constantCoeff_tateC4Formal_cube :
    PowerSeries.constantCoeff (tateC4Formal ^ 3) = 1 := by
  simpa [PowerSeries.constantCoeff] using coeff_tateC4Formal_cube_zero

theorem coeff_zero_invOfUnit_tateC4Formal_cube :
    PowerSeries.coeff 0 (PowerSeries.invOfUnit (tateC4Formal ^ 3) 1) = 1 := by
  rw [PowerSeries.coeff_invOfUnit]
  simp

theorem tateDFormal_sub_X_dvd_X_sq :
    (PowerSeries.X : PowerSeries (PadicInt 5)) ^ 2 ∣ (tateDFormal - PowerSeries.X) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  interval_cases m
  · have hD : PowerSeries.constantCoeff tateDFormal = 0 := by
      simpa [PowerSeries.constantCoeff] using coeff_tateDFormal_zero
    have hX : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries (PadicInt 5)) = 0 := by
      simp
    simp [hD, hX]
  · simp [PowerSeries.coeff_X, coeff_tateDFormal_one]

noncomputable def tateHFormal : PowerSeries (PadicInt 5) :=
  tateDFormal * PowerSeries.invOfUnit (tateC4Formal ^ 3) 1

theorem coeff_tateHFormal_zero : PowerSeries.coeff 0 tateHFormal = 0 := by
  rw [tateHFormal, coeff_zero_mul_powerSeries, coeff_tateDFormal_zero]
  ring

theorem coeff_tateHFormal_one : PowerSeries.coeff 1 tateHFormal = 1 := by
  rw [tateHFormal, coeff_one_mul_powerSeries, coeff_tateDFormal_zero,
    coeff_tateDFormal_one, coeff_zero_invOfUnit_tateC4Formal_cube]
  ring

theorem tateHFormal_sub_X_dvd_X_sq :
    (PowerSeries.X : PowerSeries (PadicInt 5)) ^ 2 ∣ (tateHFormal - PowerSeries.X) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  interval_cases m
  · have hD : PowerSeries.constantCoeff tateHFormal = 0 := by
      simpa [PowerSeries.constantCoeff] using coeff_tateHFormal_zero
    have hX : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries (PadicInt 5)) = 0 := by
      simp
    simp [hD, hX]
  · simp [PowerSeries.coeff_X, coeff_tateHFormal_one]

end

end LeanFormal.IUT.PAdicAnalytic
