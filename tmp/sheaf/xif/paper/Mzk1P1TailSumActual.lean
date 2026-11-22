/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.Geometry.RigidTateSeries
import Mathlib.Tactic

/-! # P1 tail Lipschitz: q^n u vs q^n v -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P1TailSumActual
open LeanFormal.IUT

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem xTerm_diff_norm_le (a b : K)
    (ha : ‖1 - a‖ = 1) (hb : ‖1 - b‖ = 1) (hab : ‖a * b‖ ≤ 1) :
    ‖a / (1 - a) ^ 2 - b / (1 - b) ^ 2‖ ≤ ‖a - b‖ := by
  have h1a : 1 - a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    norm_num at ha
  have h1b : 1 - b ≠ 0 := by
    intro h
    rw [h, norm_zero] at hb
    norm_num at hb
  have hfac : a / (1 - a) ^ 2 - b / (1 - b) ^ 2 =
      (a - b) * (1 - a * b) / ((1 - a) ^ 2 * (1 - b) ^ 2) := by
    field_simp [h1a, h1b]
    ring
  have hnum : ‖1 - a * b‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (1 : K) (-(a * b))
    calc
      ‖1 - a * b‖ = ‖1 + (-(a * b))‖ := by ring_nf
      _ ≤ max ‖(1 : K)‖ ‖a * b‖ := by simpa using h
      _ = 1 := by rw [norm_one, max_eq_left hab]
  have hden : ‖(1 - a) ^ 2 * (1 - b) ^ 2‖ = 1 := by
    rw [norm_mul, norm_pow, norm_pow, ha, hb]
    norm_num
  rw [hfac, norm_div, norm_mul, hden]
  rw [div_one]
  exact mul_le_of_le_one_right (norm_nonneg _) hnum



variable (P : RigidTate.Parameter (K := K))

theorem xPositiveTerm_diff_norm_le (u v : RigidTate.FundamentalDomain P) (n : ℕ) :
    ‖RigidTate.xPositiveTerm P u n - RigidTate.xPositiveTerm P v n‖ ≤
      ‖P.q‖ ^ (n : ℤ) * ‖u.1 - v.1‖ := by
  have hnorm_u : ‖RigidTate.positiveArgument P u n‖ < 1 :=
    RigidTate.Argument.positiveArgument_norm_lt_one P u n
  have hnorm_v : ‖RigidTate.positiveArgument P v n‖ < 1 :=
    RigidTate.Argument.positiveArgument_norm_lt_one P v n
  have ha := RigidTate.Argument.positiveArgument_sub_one_norm P u n
  have hb := RigidTate.Argument.positiveArgument_sub_one_norm P v n
  have hab : ‖RigidTate.positiveArgument P u n * RigidTate.positiveArgument P v n‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ hnorm_u.le hnorm_v.le
  have h := xTerm_diff_norm_le (RigidTate.positiveArgument P u n)
    (RigidTate.positiveArgument P v n) ha hb hab
  have harg : RigidTate.positiveArgument P u n - RigidTate.positiveArgument P v n =
      P.q ^ (n : ℤ) * (u.1 - v.1) := by
    simp [RigidTate.positiveArgument]; ring
  have h' : ‖RigidTate.xPositiveTerm P u n - RigidTate.xPositiveTerm P v n‖ ≤
      ‖P.q ^ (n : ℤ) * (u.1 - v.1)‖ := by
    simpa [RigidTate.xPositiveTerm] using h
  calc
    ‖RigidTate.xPositiveTerm P u n - RigidTate.xPositiveTerm P v n‖
        ≤ ‖P.q ^ (n : ℤ) * (u.1 - v.1)‖ := h'
    _ = ‖P.q‖ ^ (n : ℤ) * ‖u.1 - v.1‖ := by rw [norm_mul, norm_zpow]

theorem xPositiveTail_diff_norm_le (u v : RigidTate.FundamentalDomain P) :
    ‖(∑' n : ℕ, RigidTate.xPositiveTerm P u (n + 1)) -
      (∑' n : ℕ, RigidTate.xPositiveTerm P v (n + 1))‖ ≤
      (1 - ‖P.q‖)⁻¹ * ‖u.1 - v.1‖ := by
  have hq : ‖P.q‖ < 1 := P.q_norm_lt_one
  have hq0 : 0 ≤ ‖P.q‖ := norm_nonneg _
  have hden : 0 < 1 - ‖P.q‖ := by linarith
  let d : ℝ := ‖u.1 - v.1‖
  have hu : Summable (fun n : ℕ => RigidTate.xPositiveTerm P u (n + 1)) :=
    (RigidTate.Term.xPositiveTerm_summable P u).comp_injective
      (fun a b h => Nat.succ_injective h)
  have hv : Summable (fun n : ℕ => RigidTate.xPositiveTerm P v (n + 1)) :=
    (RigidTate.Term.xPositiveTerm_summable P v).comp_injective
      (fun a b h => Nat.succ_injective h)
  have hdiff : Summable (fun n : ℕ =>
      RigidTate.xPositiveTerm P u (n + 1) - RigidTate.xPositiveTerm P v (n + 1)) :=
    hu.sub hv
  rw [← hu.tsum_sub hv]
  have hbound : ∀ n : ℕ,
      ‖RigidTate.xPositiveTerm P u (n + 1) -
        RigidTate.xPositiveTerm P v (n + 1)‖ ≤ ‖P.q‖ ^ n * d := by
    intro n
    have h := xPositiveTerm_diff_norm_le P u v (n + 1)
    have hle : ‖P.q‖ ^ n * ‖P.q‖ ≤ ‖P.q‖ ^ n := by
      simpa using mul_le_mul_of_nonneg_left hq.le (pow_nonneg hq0 n)
    have hpow : ‖P.q‖ ^ (n + 1) = ‖P.q‖ ^ n * ‖P.q‖ := by rw [pow_succ]
    calc
      ‖RigidTate.xPositiveTerm P u (n + 1) -
        RigidTate.xPositiveTerm P v (n + 1)‖
          ≤ ‖P.q‖ ^ (n + 1) * ‖(u.1 : K) - (v.1 : K)‖ := by
              simpa [zpow_natCast] using h
      _ = ‖P.q‖ ^ n * ‖P.q‖ * d := by rw [hpow]; rfl
      _ ≤ ‖P.q‖ ^ n * d := by
          exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
  have hnormsum : Summable (fun n : ℕ =>
      ‖RigidTate.xPositiveTerm P u (n + 1) -
        RigidTate.xPositiveTerm P v (n + 1)‖) := hdiff.norm
  have hgeom : Summable (fun n : ℕ => ‖P.q‖ ^ n * d) := by
    have hqR : ‖(‖P.q‖ : ℝ)‖ < 1 := by simpa using hq
    have h := (hasSum_geometric_of_norm_lt_one hqR).mul_left d
    simpa [mul_comm] using h.summable
  calc
    ‖∑' n : ℕ, (RigidTate.xPositiveTerm P u (n + 1) -
        RigidTate.xPositiveTerm P v (n + 1))‖
        ≤ ∑' n : ℕ, ‖RigidTate.xPositiveTerm P u (n + 1) -
            RigidTate.xPositiveTerm P v (n + 1)‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ, ‖P.q‖ ^ n * d :=
        hnormsum.tsum_le_tsum hbound hgeom
    _ = (1 - ‖P.q‖)⁻¹ * d := by
        rw [show (∑' n : ℕ, ‖P.q‖ ^ n * d) = d * (∑' n : ℕ, ‖P.q‖ ^ n) by
          rw [← tsum_mul_left]; congr 1; ext n; rw [mul_comm]]
        rw [tsum_geometric_of_lt_one hq0 hq]
        ring

end LeanFormal.IUT.XiFPaper.Mzk1P1TailSumActual
