import tmp.sheaf.xif.paper.TateThetaProductAttempt
import tmp.sheaf.xif.paper.TateThetaAdditionAttempt
open LeanFormal.IUT.XiFPaper.TateThetaAdditionAttempt

noncomputable section
open Filter Topology
open LeanFormal.IUT.XiFPaper.TateThetaProductAttempt
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.TateThetaDuplicationAttempt

universe u

variable {K : Type u} [NormedField K]

/-- Actual factor expansion at `u * v`. -/
theorem S3127_tateThetaFactor_mul (q u v : K) (n : Nat) :
    tateThetaFactor q (u * v) n =
      (1 - q ^ n) * (1 - q ^ n * (u * v)) *
        (1 - q ^ n * (u * v)⁻¹) := rfl

/-- Actual product rearrangement at `u * v`: definitional product form. -/
theorem S3127_tateThetaProduct_mul (q u v : K) :
    tateThetaProduct q (u * v) =
      (1 - u * v) *
        tprod (fun n : Nat =>
          (1 - q ^ (n + 1)) *
            (1 - q ^ (n + 1) * (u * v)) *
            (1 - q ^ (n + 1) * (u * v)⁻¹)) := rfl

/-- Actual factor expansion at `u ^ 2`. -/
theorem S3127_tateThetaFactor_sq (q u : K) (n : Nat) :
    tateThetaFactor q (u ^ 2) n =
      (1 - q ^ n) * (1 - q ^ n * u ^ 2) *
        (1 - q ^ n * (u ^ 2)⁻¹) := rfl

/-- Actual product rearrangement at `u ^ 2`. -/
theorem S3127_tateThetaProduct_sq (q u : K) :
    tateThetaProduct q (u ^ 2) =
      (1 - u ^ 2) *
        tprod (fun n : Nat =>
          (1 - q ^ (n + 1)) *
            (1 - q ^ (n + 1) * u ^ 2) *
            (1 - q ^ (n + 1) * (u ^ 2)⁻¹)) := rfl

/-- Factor quotient at u*v versus u and v. -/
noncomputable def thetaFactorRatio (q u v : K) (n : Nat) : K :=
  tateThetaFactor q (u * v) (n + 1) /
    (tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1))

/-- Actual pointwise factor rearrangement: the factor at u*v is the product
of the factors at u and v times the factor quotient. -/
theorem S3127_factor_ratio (q u v : K) (n : Nat)
    (hden : tateThetaFactor q u (n + 1) *
        tateThetaFactor q v (n + 1) ≠ 0) :
    tateThetaFactor q (u * v) (n + 1) =
      tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1) *
        thetaFactorRatio q u v n := by
  unfold thetaFactorRatio
  rw [div_eq_mul_inv]
  have hcancel :
      (tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1)) *
        (tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1))⁻¹ = 1 :=
    mul_inv_cancel₀ hden
  have hcalc :
      tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1) *
          (tateThetaFactor q (u * v) (n + 1) *
            (tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1))⁻¹) =
        tateThetaFactor q (u * v) (n + 1) := by
    calc
      tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1) *
          (tateThetaFactor q (u * v) (n + 1) *
            (tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1))⁻¹)
        = tateThetaFactor q (u * v) (n + 1) *
            ((tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1)) *
              (tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1))⁻¹) := by
          ring
      _ = tateThetaFactor q (u * v) (n + 1) := by rw [hcancel, mul_one]
  exact hcalc.symm

/-- Coefficient defined by the prefactor quotient and the product of all
factor quotients. -/
noncomputable def thetaMulCoeff (q u v : K) : K :=
  ((1 - u * v) / ((1 - u) * (1 - v))) *
    tprod (fun n : Nat => thetaFactorRatio q u v n)

/-- Product-level rearrangement target with the actual factor-quotient
coefficient. -/
def TateThetaMulRearrangementTarget (q u v : K) : Prop :=
  tateThetaProduct q (u * v) =
    tateThetaProduct q u * tateThetaProduct q v * thetaMulCoeff q u v


set_option maxHeartbeats 4000000 in
theorem S3127_shifted_multipliable [CompleteSpace K]
    (q u : K) (hq : ‖q‖ < 1) :
    Multipliable (fun n : Nat => tateThetaFactor q u (n + 1)) := by
  let M : Real := max 1 (max ‖u‖ ‖u⁻¹‖)
  let C : Real := 3 * M + 3 * M ^ 2 + M ^ 3
  have hM0 : 0 <= M := le_trans zero_le_one (le_max_left _ _)
  have hC : 0 <= C := by
    dsimp [C]
    positivity
  have hCq : 0 <= C * ‖q‖ := mul_nonneg hC (norm_nonneg q)
  exact S3126_multipliable_of_norm_geometric
    (f := fun n : Nat => tateThetaFactor q u (n + 1))
    ‖q‖ (C * ‖q‖) (norm_nonneg q) hq hCq
    (fun n => by
      have h := S3126_factor_norm_bound q u hq (n + 1)
      calc
        ‖tateThetaFactor q u (n + 1) - 1‖ <= C * ‖q‖ ^ (n + 1) := by
          simpa [M, C] using h
        _ = (C * ‖q‖) * ‖q‖ ^ n := by ring)

theorem S3127_shifted_tendsto_one (q u : K) (hq : ‖q‖ < 1) :
    Tendsto (fun n : Nat => tateThetaFactor q u (n + 1)) atTop (nhds 1) := by
  exact (S3126_factor_tendsto_one q u hq).comp (tendsto_add_atTop_nat 1)

theorem S3127_shifted_denominator_eventually (q u v : K) (hq : ‖q‖ < 1) :
    ∃ N : Nat, ∀ n : Nat, N <= n ->
      (1 / 2 : Real) <= ‖tateThetaFactor q u (n + 1) *
        tateThetaFactor q v (n + 1)‖ := by
  have hmu : Tendsto (fun n : Nat => tateThetaFactor q u (n + 1))
      atTop (nhds 1) := S3127_shifted_tendsto_one q u hq
  have hmv : Tendsto (fun n : Nat => tateThetaFactor q v (n + 1))
      atTop (nhds 1) := S3127_shifted_tendsto_one q v hq
  have hmul : Tendsto (fun n : Nat =>
      tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1))
      atTop (nhds (1 * 1)) := hmu.mul hmv
  have hnorm : Tendsto (fun n : Nat =>
      ‖tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1)‖)
      atTop (nhds ‖(1 : K)‖) := by
    simpa using hmul.norm
  have hev : (fun n : Nat =>
      ‖tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1)‖)
      =ᶠ[atTop] (fun n : Nat =>
        ‖tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1)‖) := Filter.EventuallyEq.rfl
  have hpos : ∀ᶠ n : Nat in atTop,
      (1 / 2 : Real) < ‖tateThetaFactor q u (n + 1) *
        tateThetaFactor q v (n + 1)‖ := by
    have hI : Set.Ioi (1 / 2 : Real) ∈ nhds (‖(1 : K)‖) := by
      have h1 : ‖(1 : K)‖ = 1 := norm_one
      rw [h1]
      exact Ioi_mem_nhds (by norm_num)
    exact hnorm hI
  rcases (eventually_atTop.1 hpos) with ⟨N, hN⟩
  exact ⟨N, fun n hn => le_of_lt (hN n hn)⟩

noncomputable def thetaFactorNormConstant (u : K) : Real := 
  let M : Real := max 1 (max ‖u‖ ‖u⁻¹‖)
  3 * M + 3 * M ^ 2 + M ^ 3

theorem thetaFactorNormConstant_nonneg (u : K) :
    0 <= thetaFactorNormConstant u := by
  dsimp [thetaFactorNormConstant]
  positivity

theorem S3127_factor_norm_bound_shift (q u : K) (hq : ‖q‖ < 1) (n : Nat) :
    ‖tateThetaFactor q u (n + 1) - 1‖ <=
      (thetaFactorNormConstant u * ‖q‖) * ‖q‖ ^ n := by
  have h := S3126_factor_norm_bound q u hq (n + 1)
  calc
    ‖tateThetaFactor q u (n + 1) - 1‖ <=
        thetaFactorNormConstant u * ‖q‖ ^ (n + 1) := by
      simpa [thetaFactorNormConstant] using h
    _ = (thetaFactorNormConstant u * ‖q‖) * ‖q‖ ^ n := by ring

theorem S3127_numerator_norm_bound (q u v : K) (hq : ‖q‖ < 1) (n : Nat) :
    ‖tateThetaFactor q (u * v) (n + 1) -
        tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1)‖ <=
      ((thetaFactorNormConstant (u * v) * ‖q‖) +
          (thetaFactorNormConstant u * ‖q‖) +
          (thetaFactorNormConstant v * ‖q‖) +
          (thetaFactorNormConstant u * ‖q‖) *
            (thetaFactorNormConstant v * ‖q‖)) * ‖q‖ ^ n := by
  let r : Real := ‖q‖
  let Cu : Real := thetaFactorNormConstant u * r
  let Cv : Real := thetaFactorNormConstant v * r
  let Cuv : Real := thetaFactorNormConstant (u * v) * r
  have hr0 : 0 <= r := norm_nonneg q
  have hr1 : r <= 1 := le_of_lt hq
  have hCu0 : 0 <= Cu := mul_nonneg (thetaFactorNormConstant_nonneg u) hr0
  have hCv0 : 0 <= Cv := mul_nonneg (thetaFactorNormConstant_nonneg v) hr0
  have hCuv0 : 0 <= Cuv := mul_nonneg (thetaFactorNormConstant_nonneg (u * v)) hr0
  have hA := S3127_factor_norm_bound_shift q (u * v) hq n
  have hB := S3127_factor_norm_bound_shift q u hq n
  have hC := S3127_factor_norm_bound_shift q v hq n
  have hExp1 : tateThetaFactor q (u * v) (n + 1) -
      tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1) =
      (tateThetaFactor q (u * v) (n + 1) - 1) -
        (tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1) - 1) := by
    ring
  have hExp2 : tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1) - 1 =
      (tateThetaFactor q u (n + 1) - 1) +
        (tateThetaFactor q v (n + 1) - 1) +
        (tateThetaFactor q u (n + 1) - 1) *
          (tateThetaFactor q v (n + 1) - 1) := by
    ring
  have hden : ‖tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1) - 1‖ <=
      Cu * r ^ n + Cv * r ^ n + Cu * Cv * r ^ (2 * n) := by
    rw [hExp2]
    calc
      ‖(tateThetaFactor q u (n + 1) - 1) +
          (tateThetaFactor q v (n + 1) - 1) +
          (tateThetaFactor q u (n + 1) - 1) *
            (tateThetaFactor q v (n + 1) - 1)‖ <=
          ‖(tateThetaFactor q u (n + 1) - 1) +
            (tateThetaFactor q v (n + 1) - 1)‖ +
            ‖(tateThetaFactor q u (n + 1) - 1) *
              (tateThetaFactor q v (n + 1) - 1)‖ := norm_add_le _ _
      _ <= (Cu * r ^ n + Cv * r ^ n) +
            (Cu * r ^ n) * (Cv * r ^ n) := by
        gcongr
        · calc
            ‖(tateThetaFactor q u (n + 1) - 1) +
                (tateThetaFactor q v (n + 1) - 1)‖
              <= ‖tateThetaFactor q u (n + 1) - 1‖ +
                  ‖tateThetaFactor q v (n + 1) - 1‖ := norm_add_le _ _
            _ <= Cu * r ^ n + Cv * r ^ n :=
              add_le_add (by simpa [Cu, r] using hB) (by simpa [Cv, r] using hC)
        · rw [norm_mul]
          exact mul_le_mul (by simpa [Cu, r] using hB)
            (by simpa [Cv, r] using hC) (norm_nonneg _)
            (mul_nonneg hCu0 (pow_nonneg hr0 n))
      _ = Cu * r ^ n + Cv * r ^ n + Cu * Cv * r ^ (2 * n) := by ring
  have h2 : r ^ (2 * n) <= r ^ n := by
    have hle : r ^ n <= 1 := pow_le_one₀ hr0 hr1
    have hsq : (r ^ n) ^ 2 <= r ^ n := sq_le (pow_nonneg hr0 n) hle
    simpa [mul_comm, pow_mul] using hsq
  calc
    ‖tateThetaFactor q (u * v) (n + 1) -
        tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1)‖
      = ‖(tateThetaFactor q (u * v) (n + 1) - 1) -
          (tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1) - 1)‖ := by
        rw [hExp1]
    _ <= ‖tateThetaFactor q (u * v) (n + 1) - 1‖ +
          ‖tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1) - 1‖ :=
        norm_sub_le _ _
    _ <= Cuv * r ^ n + (Cu * r ^ n + Cv * r ^ n + Cu * Cv * r ^ (2 * n)) := by
        exact add_le_add (by simpa [Cuv, r] using hA) hden
    _ <= (Cuv + Cu + Cv + Cu * Cv) * r ^ n := by
        have hmul2 : Cu * Cv * r ^ (2 * n) <= Cu * Cv * r ^ n :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hCu0 hCv0)
        nlinarith [hmul2, hCu0, hCv0, hCuv0, pow_nonneg hr0 n]
    _ = ((thetaFactorNormConstant (u * v) * ‖q‖) +
          (thetaFactorNormConstant u * ‖q‖) +
          (thetaFactorNormConstant v * ‖q‖) +
          (thetaFactorNormConstant u * ‖q‖) *
            (thetaFactorNormConstant v * ‖q‖)) * ‖q‖ ^ n := by
        simp [Cu, Cv, Cuv, r]

theorem S3127_ratio_norm_bound_eventually (q u v : K) (hq : ‖q‖ < 1) :
    ∃ N : Nat, ∀ n : Nat, N <= n ->
      ‖thetaFactorRatio q u v n - 1‖ <=
        2 * ((thetaFactorNormConstant (u * v) * ‖q‖) +
          (thetaFactorNormConstant u * ‖q‖) +
          (thetaFactorNormConstant v * ‖q‖) +
          (thetaFactorNormConstant u * ‖q‖) *
            (thetaFactorNormConstant v * ‖q‖)) * ‖q‖ ^ n := by
  obtain ⟨N, hN⟩ := S3127_shifted_denominator_eventually q u v hq
  refine ⟨N, fun n hn => ?_⟩
  let r : Real := ‖q‖
  let Fu : K := tateThetaFactor q u (n + 1)
  let Fv : K := tateThetaFactor q v (n + 1)
  let Fuv : K := tateThetaFactor q (u * v) (n + 1)
  let Cnum : Real := (thetaFactorNormConstant (u * v) * r) +
    (thetaFactorNormConstant u * r) +
    (thetaFactorNormConstant v * r) +
    (thetaFactorNormConstant u * r) * (thetaFactorNormConstant v * r)
  have hdenpos : (0 : Real) < ‖Fu * Fv‖ := by
    have hhalf : (1 / 2 : Real) <= ‖Fu * Fv‖ := by
      simpa [Fu, Fv] using hN n hn
    exact lt_of_lt_of_le (by norm_num) hhalf
  have hden : Fu * Fv ≠ 0 := norm_pos_iff.mp hdenpos
  have hRsub : thetaFactorRatio q u v n - 1 =
      (Fuv - Fu * Fv) / (Fu * Fv) := by
    unfold thetaFactorRatio
    simp only [Fu, Fv, Fuv]
    rw [← div_self hden]
    rw [← sub_div]
  have hnum := S3127_numerator_norm_bound q u v hq n
  have hnum' : ‖Fuv - Fu * Fv‖ <= Cnum * r ^ n := by
    simpa [Fuv, Fu, Fv, Cnum, r] using hnum
  have hCnum0 : 0 <= Cnum := by
    have hu0 : 0 <= thetaFactorNormConstant u * r :=
      mul_nonneg (thetaFactorNormConstant_nonneg u) (norm_nonneg q)
    have hv0 : 0 <= thetaFactorNormConstant v * r :=
      mul_nonneg (thetaFactorNormConstant_nonneg v) (norm_nonneg q)
    have huv0 : 0 <= thetaFactorNormConstant (u * v) * r :=
      mul_nonneg (thetaFactorNormConstant_nonneg (u * v)) (norm_nonneg q)
    have huv2 : 0 <= (thetaFactorNormConstant u * r) *
        (thetaFactorNormConstant v * r) := mul_nonneg hu0 hv0
    dsimp [Cnum]
    nlinarith [hu0, hv0, huv0, huv2]
  have hstep1 : ‖Fuv - Fu * Fv‖ / ‖Fu * Fv‖ <= Cnum * r ^ n / ‖Fu * Fv‖ :=
    div_le_div_of_nonneg_right hnum' hdenpos.le
  have hstep2 : Cnum * r ^ n / ‖Fu * Fv‖ <= Cnum * r ^ n / (1 / 2) := by
    have hnum0 : 0 <= Cnum * r ^ n :=
      mul_nonneg hCnum0 (pow_nonneg (norm_nonneg q) n)
    exact div_le_div_of_nonneg_left hnum0 (by norm_num) (hN n hn)
  calc
    ‖thetaFactorRatio q u v n - 1‖
      = ‖(Fuv - Fu * Fv) / (Fu * Fv)‖ := by rw [hRsub]
    _ = ‖Fuv - Fu * Fv‖ / ‖Fu * Fv‖ := norm_div _ _
    _ <= Cnum * r ^ n / ‖Fu * Fv‖ := hstep1
    _ <= Cnum * r ^ n / (1 / 2) := hstep2
    _ = (2 * Cnum) * r ^ n := by ring
    _ = 2 * ((thetaFactorNormConstant (u * v) * ‖q‖) +
          (thetaFactorNormConstant u * ‖q‖) +
          (thetaFactorNormConstant v * ‖q‖) +
          (thetaFactorNormConstant u * ‖q‖) *
            (thetaFactorNormConstant v * ‖q‖)) * ‖q‖ ^ n := by
      simp [Cnum, r]

theorem S3127_multipliable_of_eventually_norm_geometric [CompleteSpace K]
    (f : Nat -> K) (r C : Real)
    (hr0 : 0 <= r) (hr : r < 1) (hC : 0 <= C)
    (N : Nat) (h : ∀ n : Nat, N <= n -> ‖f n - 1‖ <= C * r ^ n) :
    Multipliable f := by
  let g : Nat -> K := fun n => f (n + N)
  have hg : Multipliable g := by
    refine S3126_multipliable_of_norm_geometric g r (C * r ^ N)
      hr0 hr (mul_nonneg hC (pow_nonneg hr0 N)) (fun n => ?_)
    have hh := h (n + N) (Nat.le_add_left N n)
    have hrpow : r ^ (n + N) = r ^ n * r ^ N := by ring_nf
    calc
      ‖g n - 1‖ <= C * r ^ (n + N) := hh
      _ = (C * r ^ N) * r ^ n := by rw [hrpow]; ring
  exact Multipliable.comp_nat_add (f := f) (k := N) (by simpa [g] using hg)

theorem S3127_ratio_multipliable [CompleteSpace K]
    (q u v : K) (hq : ‖q‖ < 1) :
    Multipliable (fun n : Nat => thetaFactorRatio q u v n) := by
  obtain ⟨N, hN⟩ := S3127_ratio_norm_bound_eventually q u v hq
  let C : Real := 2 * ((thetaFactorNormConstant (u * v) * ‖q‖) +
    (thetaFactorNormConstant u * ‖q‖) +
    (thetaFactorNormConstant v * ‖q‖) +
    (thetaFactorNormConstant u * ‖q‖) *
      (thetaFactorNormConstant v * ‖q‖))
  have hC : 0 <= C := by
    have hu0 : 0 <= thetaFactorNormConstant u * ‖q‖ :=
      mul_nonneg (thetaFactorNormConstant_nonneg u) (norm_nonneg q)
    have hv0 : 0 <= thetaFactorNormConstant v * ‖q‖ :=
      mul_nonneg (thetaFactorNormConstant_nonneg v) (norm_nonneg q)
    have huv0 : 0 <= thetaFactorNormConstant (u * v) * ‖q‖ :=
      mul_nonneg (thetaFactorNormConstant_nonneg (u * v)) (norm_nonneg q)
    have huv2 : 0 <= (thetaFactorNormConstant u * ‖q‖) *
        (thetaFactorNormConstant v * ‖q‖) := mul_nonneg hu0 hv0
    dsimp [C]
    nlinarith [hu0, hv0, huv0, huv2]
  exact S3127_multipliable_of_eventually_norm_geometric
    (fun n : Nat => thetaFactorRatio q u v n) ‖q‖ C
    (norm_nonneg q) hq hC N (fun n hn => by
      simpa [C] using hN n hn)

set_option maxHeartbeats 4000000 in
theorem S3127_tateThetaMulRearrangementTarget_actual [CompleteSpace K]
    (q u v : K) (hq : ‖q‖ < 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hfac_u : forall n : Nat, tateThetaFactor q u (n + 1) ≠ 0)
    (hfac_v : forall n : Nat, tateThetaFactor q v (n + 1) ≠ 0) :
    TateThetaMulRearrangementTarget q u v := by
  have hmu : Multipliable (fun n : Nat => tateThetaFactor q u (n + 1)) :=
    S3127_shifted_multipliable q u hq
  have hmv : Multipliable (fun n : Nat => tateThetaFactor q v (n + 1)) :=
    S3127_shifted_multipliable q v hq
  have hmuv : Multipliable
      (fun n : Nat => tateThetaFactor q (u * v) (n + 1)) :=
    S3127_shifted_multipliable q (u * v) hq
  have hR : Multipliable (fun n : Nat => thetaFactorRatio q u v n) :=
    S3127_ratio_multipliable q u v hq
  have hpoint : forall n : Nat,
      tateThetaFactor q (u * v) (n + 1) =
        tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1) *
          thetaFactorRatio q u v n := by
    intro n
    exact S3127_factor_ratio q u v n
      (mul_ne_zero (hfac_u n) (hfac_v n))
  have hcongr :
      tprod (fun n : Nat => tateThetaFactor q (u * v) (n + 1)) =
        tprod (fun n : Nat =>
          tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1) *
            thetaFactorRatio q u v n) :=
    tprod_congr hpoint
  have hmul1 :
      tprod (fun n : Nat =>
          tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1) *
            thetaFactorRatio q u v n) =
        tprod (fun n : Nat =>
          tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1)) *
          tprod (fun n : Nat => thetaFactorRatio q u v n) :=
    Multipliable.tprod_mul (hmu.mul hmv) hR
  have hmul2 :
      tprod (fun n : Nat =>
          tateThetaFactor q u (n + 1) * tateThetaFactor q v (n + 1)) =
        tprod (fun n : Nat => tateThetaFactor q u (n + 1)) *
          tprod (fun n : Nat => tateThetaFactor q v (n + 1)) :=
    Multipliable.tprod_mul hmu hmv
  have hpref : (1 - u) * (1 - v) ≠ 0 := by
    exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hu1))
      (sub_ne_zero.mpr (Ne.symm hv1))
  unfold TateThetaMulRearrangementTarget tateThetaProduct thetaMulCoeff
  rw [hcongr, hmul1, hmul2]
  field_simp [hpref]

theorem S3127_thetaDuplicationTarget_actual [CompleteSpace K]
    (q : K) (hq : ‖q‖ < 1)
    (hu1 : forall u : K, u ≠ 1)
    (hfac : forall (u : K) (n : Nat), tateThetaFactor q u (n + 1) ≠ 0) :
    TateThetaDuplicationTarget q (fun u : K => thetaMulCoeff q u u) := by
  intro u
  have h := S3127_tateThetaMulRearrangementTarget_actual q u u hq
    (hu1 u) (hu1 u) (hfac u) (hfac u)
  unfold TateThetaMulRearrangementTarget at h
  simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using h
#check S3127_tateThetaFactor_mul
#check S3127_tateThetaProduct_mul
#check S3127_tateThetaFactor_sq
#check S3127_tateThetaProduct_sq
#print axioms S3127_tateThetaProduct_mul

#check S3127_factor_ratio
#check thetaMulCoeff
#check TateThetaMulRearrangementTarget
#print axioms S3127_factor_ratio
#print axioms S3127_tateThetaProduct_sq

end LeanFormal.IUT.XiFPaper.TateThetaDuplicationAttempt
end