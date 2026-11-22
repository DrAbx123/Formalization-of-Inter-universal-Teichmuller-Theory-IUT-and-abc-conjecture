import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic
import LeanFormal.IUT.Foundations.PAdicAnalytic.DivisorsAntidiagonalCard
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Tactic

open scoped ArithmeticFunction.sigma
open ArithmeticFunction

namespace LeanFormal.IUT.PAdicAnalytic

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Filter Nat Topology

variable {K : Type*} [NontriviallyNormedField K] [CharZero K] [IsUltrametricDist K] [CompleteSpace K]

/-- The divisor-sum q-series S_k(q) = sum_{m>=1} sigma_k(m) q^m. -/
def sigmaSeries (k : ℕ) (q : K) : K :=
  ∑' m : ℕ+, (ArithmeticFunction.sigma k (m : ℕ) : K) * q ^ (m : ℕ)
/-- Summability of the p-adic antidiagonal family. -/
theorem summable_antidiagonal_general
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (k : ℕ) {q : K} (hq : ‖q‖ < 1) :
    Summable fun c : (n : ℕ+) × {x // x ∈ (n : ℕ).divisorsAntidiagonal} ↦
      (c.2.1.2 : K) ^ k * q ^ (c.2.1.1 * c.2.1.2) := by
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
  have hx : ‖(c.2.1.2 : K)‖ ≤ 1 := hint _
  have hqle : ‖q‖ ≤ 1 := hq.le
  have hqnonneg : 0 ≤ ‖q‖ := norm_nonneg q
  calc
    ‖(c.2.1.2 : K)‖ ^ k * ‖q ^ (c.1 : ℕ)‖
        = ‖(c.2.1.2 : K)‖ ^ k * ‖q‖ ^ (c.1 : ℕ) := by
          rw [norm_pow]
    _ ≤ 1 ^ k * ‖q‖ ^ (c.1 : ℕ) := by
          exact mul_le_mul_of_nonneg_right
            (by simpa using pow_le_one₀ (norm_nonneg _) hx)
            (pow_nonneg hqnonneg _)
    _ = ‖q‖ ^ (c.1 : ℕ) := by simp

/-- P-adic product form of the antidiagonal summability. -/
theorem summable_prod_mul_pow_general
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (k : ℕ) {q : K} (hq : ‖q‖ < 1) :
    Summable fun c : (ℕ+ × ℕ+) ↦
      (c.2 : K) ^ k * q ^ (c.1 * c.2 : ℕ) := by
  have h := summable_antidiagonal_general hint k hq
  refine (sigmaAntidiagonalEquivProd.summable_iff
    (f := fun c : ℕ+ × ℕ+ => (c.2 : K) ^ k * q ^ (c.1 * c.2 : ℕ))).mp ?_
  convert h using 1
  ext c
  simp [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors]

/-- P-adic analogue of Mathlib's tsum_prod_pow_eq_tsum_sigma. -/
theorem tsum_prod_pow_eq_tsum_sigma_general
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (k : ℕ) {q : K} (hq : ‖q‖ < 1) :
    ∑' d : ℕ+, ∑' c : ℕ+, (c : K) ^ k * q ^ (d * c : ℕ) =
      ∑' e : ℕ+, (σ k e : K) * q ^ (e : ℕ) := by
  suffices ∑' c : ℕ+ × ℕ+, (c.2 : K) ^ k * q ^ (c.1 * c.2 : ℕ) =
      ∑' e : ℕ+, (σ k e : K) * q ^ (e : ℕ) by
    rwa [← (summable_prod_mul_pow_general hint k hq).tsum_prod]
  simp only [← sigmaAntidiagonalEquivProd.tsum_eq, sigmaAntidiagonalEquivProd,
    divisorsAntidiagonalFactors, PNat.mk_coe, Equiv.coe_fn_mk, sigma_eq_sum_div, cast_sum,
    cast_pow, Summable.tsum_sigma (summable_antidiagonal_general hint k hq :)]
  refine tsum_congr fun n ↦ ?_
  simpa [tsum_fintype, Finset.sum_mul,
    (n : ℕ).divisorsAntidiagonal.sum_attach (fun x : ℕ × ℕ ↦ (x.2 : K) ^ k * q ^ (x.1 * x.2)),
    sum_divisorsAntidiagonal (fun x y ↦ (y : K) ^ k * q ^ (x * y))]
      using Finset.sum_congr rfl fun i hi ↦ by rw [Nat.mul_div_cancel' (dvd_of_mem_divisors hi)]

/-- P-adic Lambert/divisor identity for arbitrary weight k. -/
theorem tsum_pow_div_one_sub_eq_tsum_sigma_general
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (k : ℕ) {q : K} (hq : ‖q‖ < 1) :
    ∑' n : ℕ+, (n : K) ^ k * q ^ (n : ℕ) / (1 - q ^ (n : ℕ)) =
      ∑' n : ℕ+, (σ k n : K) * q ^ (n : ℕ) := by
  have hgeomPN (m : ℕ+) :
      ∑' r : ℕ+, (q ^ (m : ℕ)) ^ (r : ℕ) = (1 - q ^ (m : ℕ))⁻¹ - 1 := by
    have hqpow : ‖q ^ (m : ℕ)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq (PNat.ne_zero m)
    have hxne : (1 : K) - q ^ (m : ℕ) ≠ 0 := by
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
    ∑' n : ℕ+, (n : K) ^ k * q ^ (n : ℕ) * (1 - q ^ (n : ℕ))⁻¹ =
        ∑' n : ℕ+, (n : K) ^ k * ((1 - q ^ (n : ℕ))⁻¹) * q ^ (n : ℕ) := by
      apply tsum_congr
      intro n
      ring
    _ = ∑' n : ℕ+, (n : K) ^ k * (∑' r : ℕ+, q ^ ((n : ℕ) * (r : ℕ))) := by
      apply tsum_congr
      intro n
      have h := hgeomPN n
      rw [show (∑' r : ℕ+, q ^ ((n : ℕ) * (r : ℕ))) =
          (1 - q ^ (n : ℕ))⁻¹ - 1 by
        simpa [pow_mul] using h]
      have hnne : (1 : K) - q ^ (n : ℕ) ≠ 0 := by
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
    _ = ∑' d : ℕ+, ∑' c : ℕ+, (c : K) ^ k * q ^ (d * c : ℕ) := by
      rw [show (∑' n : ℕ+, (n : K) ^ k *
            (∑' r : ℕ+, q ^ ((n : ℕ) * (r : ℕ)))) =
          ∑' n : ℕ+, ∑' r : ℕ+, (n : K) ^ k * q ^ ((n : ℕ) * (r : ℕ)) by
        apply tsum_congr
        intro n
        rw [tsum_mul_left]]
      have hs : Summable (Function.uncurry fun n r : ℕ+ =>
          (n : K) ^ k * q ^ ((n : ℕ) * (r : ℕ))) := by
        change Summable (fun p : ℕ+ × ℕ+ =>
          (p.1 : K) ^ k * q ^ ((p.1 : ℕ) * (p.2 : ℕ)))
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (summable_prod_mul_pow_general hint k hq).prod_symm
      calc
        (∑' n : ℕ+, ∑' r : ℕ+,
            (n : K) ^ k * q ^ ((n : ℕ) * (r : ℕ))) =
          ∑' r : ℕ+, ∑' n : ℕ+,
            (n : K) ^ k * q ^ ((n : ℕ) * (r : ℕ)) := hs.tsum_comm.symm
        _ = ∑' d : ℕ+, ∑' c : ℕ+, (c : K) ^ k * q ^ (d * c : ℕ) := by
          apply tsum_congr
          intro d
          apply tsum_congr
          intro c
          rw [mul_comm (c : ℕ) (d : ℕ)]
    _ = ∑' n : ℕ+, (σ k n : K) * q ^ (n : ℕ) :=
      tsum_prod_pow_eq_tsum_sigma_general hint k hq

/-- Actual Lambert coefficient identity: the Tate Lambert series S_k equals the
divisor-sum q-series. -/
theorem lambertSeries_eq_tsum_sigma_general
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (k : ℕ) {q : K} (hq : ‖q‖ < 1) :
    TateCurve.lambertSeries K k q =
      ∑' m : ℕ+, (σ k m : K) * q ^ (m : ℕ) := by
  let f : ℕ → K := fun n => (n : K) ^ k * q ^ n / (1 - q ^ n)
  have hs : Summable f := TateCurve.lambertSeries_summable K k hq
  have hf0 : f 0 = 0 := by simp [f]
  change (∑' n : ℕ, f n) = _
  rw [hs.tsum_eq_zero_add, hf0, zero_add]
  rw [← tsum_pnat_eq_tsum_succ (f := f)]
  simpa [f] using tsum_pow_div_one_sub_eq_tsum_sigma_general hint k hq

theorem lambertSeries_eq_sigmaSeries_general
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (k : ℕ) {q : K} (hq : ‖q‖ < 1) :
    TateCurve.lambertSeries K k q = sigmaSeries k q :=
  lambertSeries_eq_tsum_sigma_general hint k hq

theorem lambertSeries_eq_sigmaSeries_three
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) {q : K} (hq : ‖q‖ < 1) :
    TateCurve.lambertSeries K 3 q = sigmaSeries 3 q :=
  lambertSeries_eq_sigmaSeries_general hint 3 hq

theorem lambertSeries_eq_sigmaSeries_five
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) {q : K} (hq : ‖q‖ < 1) :
    TateCurve.lambertSeries K 5 q = sigmaSeries 5 q :=
  lambertSeries_eq_sigmaSeries_general hint 5 hq

/-- The ℕ-indexed divisor-sum q-series, matching the evaluator summation index. -/
noncomputable def sigmaSeriesNat (k : ℕ) (q : K) : K :=
  ∑' n : ℕ, (ArithmeticFunction.sigma k n : K) * q ^ n

/-- `sigmaSeriesNat` has summable coefficients under the integer-cast norm bound. -/
theorem summable_sigmaSeriesNat (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    (k : ℕ) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => (ArithmeticFunction.sigma k n : K) * q ^ n) := by
  have hgeom : Summable (fun n : ℕ => ‖q‖ ^ n) :=
    summable_geometric_of_lt_one (norm_nonneg q) hq
  refine Summable.of_norm_bounded hgeom (fun n => ?_)
  rw [norm_mul, norm_pow]
  have hsig : ‖(ArithmeticFunction.sigma k n : K)‖ ≤ 1 := hint _
  calc
    ‖(ArithmeticFunction.sigma k n : K)‖ * ‖q‖ ^ n ≤ 1 * ‖q‖ ^ n :=
      mul_le_mul_of_nonneg_right hsig (pow_nonneg (norm_nonneg q) n)
    _ = ‖q‖ ^ n := one_mul _

theorem sigmaSeriesNat_eq_sigmaSeries (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    (k : ℕ) {q : K} (hq : ‖q‖ < 1) :
    sigmaSeriesNat k q = sigmaSeries k q := by
  let f : ℕ → K := fun n => (ArithmeticFunction.sigma k n : K) * q ^ n
  have hs : Summable f := summable_sigmaSeriesNat hint k hq
  have hf0 : f 0 = 0 := by simp [f]
  have hsplit := hs.tsum_eq_zero_add
  rw [hf0, zero_add] at hsplit
  change (∑' n : ℕ, f n) = ∑' n : ℕ+, f n
  rw [tsum_pnat_eq_tsum_succ (f := f), ← hsplit]

theorem lambertSeries_eq_tsum_sigma_nat_general
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (k : ℕ) {q : K} (hq : ‖q‖ < 1) :
    TateCurve.lambertSeries K k q =
      ∑' n : ℕ, (ArithmeticFunction.sigma k n : K) * q ^ n := by
  rw [lambertSeries_eq_tsum_sigma_general hint k hq]
  let f : ℕ → K := fun n => (ArithmeticFunction.sigma k n : K) * q ^ n
  have hs : Summable f := summable_sigmaSeriesNat hint k hq
  have hf0 : f 0 = 0 := by simp [f]
  have hsplit := hs.tsum_eq_zero_add
  rw [hf0, zero_add] at hsplit
  rw [tsum_pnat_eq_tsum_succ (f := f), ← hsplit]

theorem lambertSeries_eq_sigmaSeriesNat_general
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (k : ℕ) {q : K} (hq : ‖q‖ < 1) :
    TateCurve.lambertSeries K k q = sigmaSeriesNat k q :=
  lambertSeries_eq_tsum_sigma_nat_general hint k hq

theorem lambertSeries_eq_tsum_sigma_nat_three
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) {q : K} (hq : ‖q‖ < 1) :
    TateCurve.lambertSeries K 3 q =
      ∑' n : ℕ, (ArithmeticFunction.sigma 3 n : K) * q ^ n :=
  lambertSeries_eq_tsum_sigma_nat_general hint 3 hq

theorem lambertSeries_eq_tsum_sigma_nat_five
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) {q : K} (hq : ‖q‖ < 1) :
    TateCurve.lambertSeries K 5 q =
      ∑' n : ℕ, (ArithmeticFunction.sigma 5 n : K) * q ^ n :=
  lambertSeries_eq_tsum_sigma_nat_general hint 5 hq

end

end LeanFormal.IUT.PAdicAnalytic
