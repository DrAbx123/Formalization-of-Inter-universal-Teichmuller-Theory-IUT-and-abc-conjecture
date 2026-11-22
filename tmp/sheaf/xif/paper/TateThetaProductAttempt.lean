import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

noncomputable section
open Filter Topology
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.TateThetaProductAttempt

universe u

variable {K : Type u} [NormedField K]

/-- The n-th factor of the Jacobi theta product. -/
noncomputable def tateThetaFactor (q u : K) (n : Nat) : K :=
  (1 - q ^ n) * (1 - q ^ n * u) * (1 - q ^ n * u⁻¹)

/-- The theta product, with the prefactor `(1-u)`. -/
noncomputable def tateThetaProduct (q u : K) : K :=
  (1 - u) * tprod (fun n : Nat => tateThetaFactor q u (n + 1))

/-- Exact convergence target for the theta product. -/
def S3126ThetaProductConvergent (q u : K) : Prop :=
  Multipliable (fun n : Nat => tateThetaFactor q u n)

theorem S3126_factor_tendsto_one (q u : K) (hq : ‖q‖ < 1) :
    Tendsto (fun n : Nat => tateThetaFactor q u n) atTop (nhds 1) := by
  have hqpow : Tendsto (fun n : Nat => q ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
  have h1 : Tendsto (fun n : Nat => 1 - q ^ n) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hqpow
  have h2 : Tendsto (fun n : Nat => 1 - q ^ n * u) atTop (nhds (1 - 0 * u)) :=
    tendsto_const_nhds.sub (hqpow.mul_const u)
  have h3 : Tendsto (fun n : Nat => 1 - q ^ n * u⁻¹) atTop (nhds (1 - 0 * u⁻¹)) :=
    tendsto_const_nhds.sub (hqpow.mul_const u⁻¹)
  have hmul := (h1.mul h2).mul h3
  simpa [tateThetaFactor] using hmul

#check tateThetaFactor
#check tateThetaProduct
#check S3126ThetaProductConvergent
#check S3126_factor_tendsto_one
theorem S3126_factor_summable_of_geometric_bound [CompleteSpace K]
    (q u : K) (hq : ‖q‖ < 1) (C : Real) (hC : 0 <= C)
    (h : forall n : Nat, ‖tateThetaFactor q u n - 1‖ <= C * ‖q‖ ^ n) :
    Summable (fun n : Nat => tateThetaFactor q u n - 1) := by
  have hgeom0 : Summable (fun n : Nat => (‖q‖ ^ n : Real)) :=
    summable_geometric_of_norm_lt_one (K := Real) (by simpa using hq)
  have hgeom : Summable (fun n : Nat => C * ‖q‖ ^ n) :=
    hgeom0.mul_left C
  exact Summable.of_norm_bounded hgeom (fun n => h n)

theorem S3126_multipliable_of_geometric_bound [CompleteSpace K]
    (q u : K) (hq : ‖q‖ < 1) (C : Real) (hC : 0 <= C)
    (h : forall n : Nat, ‖tateThetaFactor q u n - 1‖ <= C * ‖q‖ ^ n) :
    Multipliable (fun n : Nat => tateThetaFactor q u n) := by
  have hf : Summable (fun n : Nat => ‖tateThetaFactor q u n - 1‖) := by
    have hgeom0 : Summable (fun n : Nat => (‖q‖ ^ n : Real)) :=
      summable_geometric_of_norm_lt_one (K := Real) (by simpa using hq)
    refine Summable.of_norm_bounded (hgeom0.mul_left C) (fun n => ?_)
    simpa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (pow_nonneg (norm_nonneg q) n))]
      using h n
  simpa [sub_add_cancel] using
    (multipliable_one_add_of_summable (f := fun n : Nat => tateThetaFactor q u n - 1) hf)

theorem S3126_factor_norm_bound (q u : K) (hq : ‖q‖ < 1) (n : Nat) :
    ‖tateThetaFactor q u n - 1‖ <=
      (3 * (max 1 (max ‖u‖ ‖u⁻¹‖)) +
        3 * (max 1 (max ‖u‖ ‖u⁻¹‖)) ^ 2 +
        (max 1 (max ‖u‖ ‖u⁻¹‖)) ^ 3) * ‖q‖ ^ n := by
  let M : Real := max 1 (max ‖u‖ ‖u⁻¹‖)
  let r : Real := ‖q‖
  have hM1 : 1 <= M := le_max_left _ _
  have hMu : ‖u‖ <= M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hMui : ‖u⁻¹‖ <= M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hr0 : 0 <= r := norm_nonneg q
  have hr1 : r <= 1 := le_of_lt hq
  have ha : ‖q ^ n‖ <= M * r ^ n := by
    rw [norm_pow]
    have := mul_le_mul_of_nonneg_right hM1 (pow_nonneg hr0 n)
    simpa [r, mul_comm] using this
  have hb : ‖q ^ n * u‖ <= M * r ^ n := by
    rw [norm_mul, norm_pow]
    have h := mul_le_mul_of_nonneg_left hMu (pow_nonneg hr0 n)
    nlinarith [h]
  have hc : ‖q ^ n * u⁻¹‖ <= M * r ^ n := by
    rw [norm_mul, norm_pow]
    have h := mul_le_mul_of_nonneg_left hMui (pow_nonneg hr0 n)
    nlinarith [h]
  have hab : ‖q ^ n * (q ^ n * u)‖ <= M ^ 2 * r ^ (2 * n) := by
    rw [norm_mul]
    have h := mul_le_mul ha hb (norm_nonneg _) (by positivity)
    calc ‖q ^ n‖ * ‖q ^ n * u‖ <= (M * r ^ n) * (M * r ^ n) := h
      _ = M ^ 2 * r ^ (2 * n) := by rw [pow_two, pow_mul]; ring
  have hac : ‖q ^ n * (q ^ n * u⁻¹)‖ <= M ^ 2 * r ^ (2 * n) := by
    rw [norm_mul]
    have h := mul_le_mul ha hc (norm_nonneg _) (by positivity)
    calc ‖q ^ n‖ * ‖q ^ n * u⁻¹‖ <= (M * r ^ n) * (M * r ^ n) := h
      _ = M ^ 2 * r ^ (2 * n) := by rw [pow_two, pow_mul]; ring
  have hbc : ‖(q ^ n * u) * (q ^ n * u⁻¹)‖ <= M ^ 2 * r ^ (2 * n) := by
    rw [norm_mul]
    have h := mul_le_mul hb hc (norm_nonneg _) (by positivity)
    calc ‖q ^ n * u‖ * ‖q ^ n * u⁻¹‖ <= (M * r ^ n) * (M * r ^ n) := h
      _ = M ^ 2 * r ^ (2 * n) := by rw [pow_two, pow_mul]; ring
  have habc : ‖(q ^ n) * (q ^ n * u) * (q ^ n * u⁻¹)‖ <= M ^ 3 * r ^ (3 * n) := by
    rw [norm_mul, norm_mul]
    have h := mul_le_mul (mul_le_mul ha hb (norm_nonneg _) (by positivity)) hc (norm_nonneg _) (by positivity)
    calc (‖q ^ n‖ * ‖q ^ n * u‖) * ‖q ^ n * u⁻¹‖
        <= ((M * r ^ n) * (M * r ^ n)) * (M * r ^ n) := h
      _ = M ^ 3 * r ^ (3 * n) := by rw [pow_succ]; ring_nf
  have hexp : tateThetaFactor q u n - 1 =
      -((q ^ n) + (q ^ n * u) + (q ^ n * u⁻¹)) +
        ((q ^ n) * (q ^ n * u) + (q ^ n) * (q ^ n * u⁻¹) +
          (q ^ n * u) * (q ^ n * u⁻¹)) -
        ((q ^ n) * (q ^ n * u) * (q ^ n * u⁻¹)) := by
    simp [tateThetaFactor]
    ring
  rw [hexp]
  have hnorm : ‖-((q ^ n) + (q ^ n * u) + (q ^ n * u⁻¹)) +
        ((q ^ n) * (q ^ n * u) + (q ^ n) * (q ^ n * u⁻¹) +
          (q ^ n * u) * (q ^ n * u⁻¹)) -
        ((q ^ n) * (q ^ n * u) * (q ^ n * u⁻¹))‖ <=
      (‖q ^ n‖ + ‖q ^ n * u‖ + ‖q ^ n * u⁻¹‖) +
        ((‖q ^ n * (q ^ n * u)‖ + ‖q ^ n * (q ^ n * u⁻¹)‖ +
          ‖(q ^ n * u) * (q ^ n * u⁻¹)‖)) +
        ‖(q ^ n) * (q ^ n * u) * (q ^ n * u⁻¹)‖ := by
    calc
      _ <= ‖-((q ^ n) + (q ^ n * u) + (q ^ n * u⁻¹)) +
          ((q ^ n) * (q ^ n * u) + (q ^ n) * (q ^ n * u⁻¹) +
            (q ^ n * u) * (q ^ n * u⁻¹))‖ +
          ‖(q ^ n) * (q ^ n * u) * (q ^ n * u⁻¹)‖ := norm_sub_le _ _
      _ <= (‖-((q ^ n) + (q ^ n * u) + (q ^ n * u⁻¹))‖ +
          ‖(q ^ n) * (q ^ n * u) + (q ^ n) * (q ^ n * u⁻¹) +
            (q ^ n * u) * (q ^ n * u⁻¹)‖) +
          ‖(q ^ n) * (q ^ n * u) * (q ^ n * u⁻¹)‖ := by
            gcongr; exact norm_add_le _ _
      _ <= ((‖(q ^ n) + (q ^ n * u) + (q ^ n * u⁻¹)‖) +
          (‖(q ^ n) * (q ^ n * u)‖ + ‖(q ^ n) * (q ^ n * u⁻¹)‖ +
            ‖(q ^ n * u) * (q ^ n * u⁻¹)‖)) +
          ‖(q ^ n) * (q ^ n * u) * (q ^ n * u⁻¹)‖ := by
            gcongr
            · exact le_of_eq (norm_neg ((q ^ n) + (q ^ n * u) + (q ^ n * u⁻¹)))
            · calc
                ‖(q ^ n) * (q ^ n * u) + (q ^ n) * (q ^ n * u⁻¹) +
                    (q ^ n * u) * (q ^ n * u⁻¹)‖
                  <= ‖(q ^ n) * (q ^ n * u) + (q ^ n) * (q ^ n * u⁻¹)‖ +
                    ‖(q ^ n * u) * (q ^ n * u⁻¹)‖ := norm_add_le _ _
                _ <= (‖(q ^ n) * (q ^ n * u)‖ + ‖(q ^ n) * (q ^ n * u⁻¹)‖) +
                    ‖(q ^ n * u) * (q ^ n * u⁻¹)‖ := by
                      gcongr; exact norm_add_le _ _
      _ <= ((‖q ^ n‖ + ‖q ^ n * u‖ + ‖q ^ n * u⁻¹‖) +
          (‖(q ^ n) * (q ^ n * u)‖ + ‖(q ^ n) * (q ^ n * u⁻¹)‖ +
            ‖(q ^ n * u) * (q ^ n * u⁻¹)‖)) +
          ‖(q ^ n) * (q ^ n * u) * (q ^ n * u⁻¹)‖ := by
            gcongr
            calc
              ‖(q ^ n) + (q ^ n * u) + (q ^ n * u⁻¹)‖
                <= ‖(q ^ n) + (q ^ n * u)‖ + ‖(q ^ n * u⁻¹)‖ := norm_add_le _ _
              _ <= (‖q ^ n‖ + ‖q ^ n * u‖) + ‖q ^ n * u⁻¹‖ := by
                gcongr; exact norm_add_le _ _
  have hle : r ^ n <= 1 := pow_le_one₀ hr0 hr1
  have hsq : (r ^ n) ^ 2 <= r ^ n := sq_le (pow_nonneg hr0 n) hle
  have hcube : (r ^ n) ^ 3 <= r ^ n := by
    calc (r ^ n) ^ 3 = (r ^ n) ^ 2 * (r ^ n) := by ring
      _ <= (r ^ n) ^ 2 := mul_le_of_le_one_right (sq_nonneg _) hle
      _ <= r ^ n := hsq
  have hr2 : r ^ (2 * n) <= r ^ n := by
    simpa [mul_comm, pow_mul] using hsq
  have hr3 : r ^ (3 * n) <= r ^ n := by
    simpa [mul_comm, pow_mul] using hcube
  have h2 : M ^ 2 * r ^ (2 * n) <= M ^ 2 * r ^ n :=
    mul_le_mul_of_nonneg_left hr2 (sq_nonneg M)
  have h3 : M ^ 3 * r ^ (3 * n) <= M ^ 3 * r ^ n :=
    mul_le_mul_of_nonneg_left hr3 (pow_nonneg (le_trans zero_le_one hM1) 3)
  have hsumle : (‖q ^ n‖ + ‖q ^ n * u‖ + ‖q ^ n * u⁻¹‖) +
        (‖(q ^ n) * (q ^ n * u)‖ + ‖(q ^ n) * (q ^ n * u⁻¹)‖ +
          ‖(q ^ n * u) * (q ^ n * u⁻¹)‖) +
        ‖(q ^ n) * (q ^ n * u) * (q ^ n * u⁻¹)‖ <=
      (3 * M + 3 * M ^ 2 + M ^ 3) * r ^ n := by
    have h123 : ‖q ^ n‖ + ‖q ^ n * u‖ + ‖q ^ n * u⁻¹‖ <= 3 * (M * r ^ n) := by
      linarith [ha, hb, hc]
    have h456 : ‖(q ^ n) * (q ^ n * u)‖ + ‖(q ^ n) * (q ^ n * u⁻¹)‖ +
          ‖(q ^ n * u) * (q ^ n * u⁻¹)‖ <= 3 * (M ^ 2 * r ^ n) := by
      linarith [hab, hac, hbc, h2]
    have h7 : ‖(q ^ n) * (q ^ n * u) * (q ^ n * u⁻¹)‖ <= M ^ 3 * r ^ n := by
      linarith [habc, h3]
    calc
      (‖q ^ n‖ + ‖q ^ n * u‖ + ‖q ^ n * u⁻¹‖) +
          (‖(q ^ n) * (q ^ n * u)‖ + ‖(q ^ n) * (q ^ n * u⁻¹)‖ +
            ‖(q ^ n * u) * (q ^ n * u⁻¹)‖) +
          ‖(q ^ n) * (q ^ n * u) * (q ^ n * u⁻¹)‖
        <= 3 * (M * r ^ n) + 3 * (M ^ 2 * r ^ n) + M ^ 3 * r ^ n := by
          linarith [h123, h456, h7]
      _ = (3 * M + 3 * M ^ 2 + M ^ 3) * r ^ n := by ring
  exact hnorm.trans hsumle

theorem S3126_thetaProduct_multipliable [CompleteSpace K]
    (q u : K) (hq : ‖q‖ < 1) :
    Multipliable (fun n : Nat => tateThetaFactor q u n) := by
  let M : Real := max 1 (max ‖u‖ ‖u⁻¹‖)
  let C : Real := 3 * M + 3 * M ^ 2 + M ^ 3
  have hM0 : 0 <= M := le_trans zero_le_one (le_max_left _ _)
  have hC : 0 <= C := by
    dsimp [C]
    positivity
  exact S3126_multipliable_of_geometric_bound q u hq C hC
    (fun n => S3126_factor_norm_bound q u hq n)

theorem S3126_thetaProduct_factor_summable [CompleteSpace K]
    (q u : K) (hq : ‖q‖ < 1) :
    Summable (fun n : Nat => ‖tateThetaFactor q u n - 1‖) := by
  let M : Real := max 1 (max ‖u‖ ‖u⁻¹‖)
  let C : Real := 3 * M + 3 * M ^ 2 + M ^ 3
  have hM0 : 0 <= M := le_trans zero_le_one (le_max_left _ _)
  have hC : 0 <= C := by
    dsimp [C]
    positivity
  have hgeom0 : Summable (fun n : Nat => (‖q‖ ^ n : Real)) :=
    summable_geometric_of_norm_lt_one (K := Real) (by simpa using hq)
  refine Summable.of_norm_bounded (hgeom0.mul_left C) (fun n => ?_)
  simpa [M, C, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hC (pow_nonneg (norm_nonneg q) n))]
    using (S3126_factor_norm_bound q u hq n :
      ‖tateThetaFactor q u n - 1‖ <= C * ‖q‖ ^ n)

theorem S3126_thetaProduct_nonzero [CompleteSpace K]
    (q u : K) (hq : ‖q‖ < 1) (hu : u ≠ 1)
    (hfac : forall n : Nat, tateThetaFactor q u (n + 1) ≠ 0) :
    tateThetaProduct q u ≠ 0 := by
  unfold tateThetaProduct
  apply mul_ne_zero (sub_ne_zero.mpr (Ne.symm hu))
  have hf : Summable (fun n : Nat => ‖tateThetaFactor q u (n + 1) - 1‖) :=
    (summable_nat_add_iff 1).mpr (S3126_thetaProduct_factor_summable q u hq)
  have hfac' : forall n : Nat, 1 + (tateThetaFactor q u (n + 1) - 1) ≠ 0 := by
    intro n
    simpa using hfac n
  simpa using
    (tprod_one_add_ne_zero_of_summable
      (f := fun n : Nat => tateThetaFactor q u (n + 1) - 1) hfac' hf)

theorem S3126_factor_ne_zero
    (q u : K) (n : Nat)
    (h1 : q ^ n ≠ 1)
    (h2 : q ^ n * u ≠ 1)
    (h3 : q ^ n * u⁻¹ ≠ 1) :
    tateThetaFactor q u n ≠ 0 := by
  unfold tateThetaFactor
  exact mul_ne_zero
    (mul_ne_zero (sub_ne_zero.mpr (Ne.symm h1)) (sub_ne_zero.mpr (Ne.symm h2)))
    (sub_ne_zero.mpr (Ne.symm h3))

theorem S3126_thetaProduct_nonzero_of_poles [CompleteSpace K]
    (q u : K) (hq : ‖q‖ < 1) (hu : u ≠ 1)
    (h1 : forall n : Nat, q ^ (n + 1) ≠ 1)
    (h2 : forall n : Nat, q ^ (n + 1) * u ≠ 1)
    (h3 : forall n : Nat, q ^ (n + 1) * u⁻¹ ≠ 1) :
    tateThetaProduct q u ≠ 0 := by
  apply S3126_thetaProduct_nonzero q u hq hu
  intro n
  exact S3126_factor_ne_zero q u (n + 1) (h1 n) (h2 n) (h3 n)


theorem S3126_multipliable_of_norm_geometric [CompleteSpace K]
    (f : Nat -> K) (r : Real) (C : Real)
    (hr0 : 0 <= r) (hr : r < 1) (hC : 0 <= C)
    (h : forall n : Nat, ‖f n - 1‖ <= C * r ^ n) :
    Multipliable f := by
  have hgeom0 : Summable (fun n : Nat => (r ^ n : Real)) :=
    summable_geometric_of_lt_one hr0 hr
  have hf : Summable (fun n : Nat => ‖f n - 1‖) := by
    refine Summable.of_norm_bounded (hgeom0.mul_left C) (fun n => ?_)
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hC (pow_nonneg (norm_nonneg r) n))]
      using h n
  simpa using
    (multipliable_one_add_of_summable
      (f := fun n : Nat => f n - 1) hf)
#check multipliable_one_add_of_summable
#check tprod_one_add_ne_zero_of_summable
#check summable_geometric_of_norm_lt_one
#print axioms S3126_factor_tendsto_one

end LeanFormal.IUT.XiFPaper.TateThetaProductAttempt
end