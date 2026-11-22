/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1TailSumFinalActual
import LeanFormal.IUT.Foundations.Geometry.RigidTateSeries
import Mathlib.Tactic

/-! # P1 negative tail: large-argument difference bounds -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P1NegativeTailActual
open LeanFormal.IUT

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (P : RigidTate.Parameter (K := K))

theorem xTerm_diff_norm_le_large (a b : K)
    (ha : ‖1 - a‖ = ‖a‖) (hb : ‖1 - b‖ = ‖b‖)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : ‖1 - a * b‖ ≤ ‖a * b‖) :
    ‖a / (1 - a) ^ 2 - b / (1 - b) ^ 2‖ ≤
      ‖a - b‖ * ‖a * b‖ / (‖a‖ ^ 2 * ‖b‖ ^ 2) := by
  have h1a : 1 - a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    have : ‖a‖ = 0 := by simpa using ha.symm
    exact ha0 (norm_eq_zero.mp this)
  have h1b : 1 - b ≠ 0 := by
    intro h
    rw [h, norm_zero] at hb
    have : ‖b‖ = 0 := by simpa using hb.symm
    exact hb0 (norm_eq_zero.mp this)
  have hfac : a / (1 - a) ^ 2 - b / (1 - b) ^ 2 =
      (a - b) * (1 - a * b) / ((1 - a) ^ 2 * (1 - b) ^ 2) := by
    field_simp [h1a, h1b]
    ring
  rw [hfac, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, ha, hb]
  have hden : 0 < ‖a‖ ^ 2 * ‖b‖ ^ 2 := by positivity
  apply div_le_div_of_nonneg_right ?_ hden.le
  exact mul_le_mul_of_nonneg_left hab (norm_nonneg _)



theorem norm_negativeArgument (u : RigidTate.FundamentalDomain P) (n : ℕ) :
    ‖RigidTate.negativeArgument P u n‖ =
      ‖P.q‖ ^ (-(n + 1 : ℤ)) * ‖(u.1 : K)‖ := by
  rw [RigidTate.Argument.negativeArgument_norm, zpow_neg]

theorem norm_negativeArgument_mul (u v : RigidTate.FundamentalDomain P) (n : ℕ) :
    ‖RigidTate.negativeArgument P u n‖ *
      ‖RigidTate.negativeArgument P v n‖ =
      (‖P.q‖ ^ (-(n + 1 : ℤ))) ^ 2 * (‖u.1‖ * ‖v.1‖) := by
  rw [norm_negativeArgument (P := P) u n, norm_negativeArgument (P := P) v n]
  ring_nf

theorem xNegativeTerm_diff_norm_le (u v : RigidTate.FundamentalDomain P) (n : ℕ) :
    ‖RigidTate.xNegativeTerm P u n - RigidTate.xNegativeTerm P v n‖ ≤
      (‖P.q‖ ^ (n + 1 : ℤ) / (‖(u.1 : K)‖ * ‖(v.1 : K)‖)) *
        ‖(u.1 : K) - (v.1 : K)‖ := by
  let a := RigidTate.negativeArgument P u n
  let b := RigidTate.negativeArgument P v n
  have ha : ‖1 - a‖ = ‖a‖ := RigidTate.Argument.negativeArgument_sub_one_norm P u n
  have hb : ‖1 - b‖ = ‖b‖ := RigidTate.Argument.negativeArgument_sub_one_norm P v n
  have ha0 : a ≠ 0 := RigidTate.Argument.negativeArgument_ne_zero P u n
  have hb0 : b ≠ 0 := RigidTate.Argument.negativeArgument_ne_zero P v n
  have hgt_a := RigidTate.Argument.negativeArgument_norm_gt_one P u n
  have hgt_b := RigidTate.Argument.negativeArgument_norm_gt_one P v n
  have hab : ‖1 - a * b‖ ≤ ‖a * b‖ := by
    have h := IsUltrametricDist.norm_add_le_max (1 : K) (-(a * b))
    have hprod : 1 ≤ ‖a * b‖ := by
      rw [norm_mul]
      nlinarith [norm_nonneg a, norm_nonneg b, hgt_a, hgt_b]
    calc
      ‖1 - a * b‖ = ‖1 + (-(a * b))‖ := by ring_nf
      _ ≤ max ‖(1 : K)‖ ‖a * b‖ := by simpa using h
      _ = ‖a * b‖ := by rw [norm_one, max_eq_right hprod]
  have h := xTerm_diff_norm_le_large a b ha hb ha0 hb0 hab
  have hdiff : ‖a - b‖ = ‖P.q‖ ^ (-(n + 1 : ℤ)) *
      ‖(u.1 : K) - (v.1 : K)‖ := by
    have harg : a - b = P.q ^ (-(n + 1 : ℤ)) * (u.1 - v.1) := by
      simp only [a, b, RigidTate.negativeArgument]
      have hcast : (↑(n + 1) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
      rw [hcast]
      ring
    rw [harg, norm_mul, RigidTate.Parameter.norm_q_zpow]
  have ha_norm := norm_negativeArgument (P := P) u n
  have hb_norm := norm_negativeArgument (P := P) v n
  have hqne : ‖P.q‖ ^ (-(n + 1 : ℤ)) ≠ 0 := zpow_ne_zero _ P.q_norm_ne_zero
  have hune : ‖(u.1 : K)‖ ≠ 0 := norm_ne_zero_iff.mpr (RigidTate.FundamentalDomain.ne_zero P u)
  have hvne : ‖(v.1 : K)‖ ≠ 0 := norm_ne_zero_iff.mpr (RigidTate.FundamentalDomain.ne_zero P v)
  have hratio : ‖a - b‖ * ‖a * b‖ / (‖a‖ ^ 2 * ‖b‖ ^ 2) =
      ‖a - b‖ / (‖a‖ * ‖b‖) := by
    rw [norm_mul]
    field_simp [ha_norm, hb_norm, hune, hvne]
  calc
    ‖RigidTate.xNegativeTerm P u n - RigidTate.xNegativeTerm P v n‖
        = ‖a / (1 - a) ^ 2 - b / (1 - b) ^ 2‖ := rfl
    _ ≤ ‖a - b‖ * ‖a * b‖ / (‖a‖ ^ 2 * ‖b‖ ^ 2) := h
    _ = ‖a - b‖ / (‖a‖ * ‖b‖) := hratio
    _ = (‖P.q‖ ^ (n + 1 : ℤ) / (‖(u.1 : K)‖ * ‖(v.1 : K)‖)) *
          ‖(u.1 : K) - (v.1 : K)‖ := by
        rw [hdiff, ha_norm, hb_norm]
        field_simp [hqne, hune, hvne]
        have hz : ‖P.q‖ ^ (-(↑n + 1 : ℤ)) * ‖P.q‖ ^ (↑n + 1 : ℤ) = 1 := by
          rw [← zpow_add₀ P.q_norm_ne_zero]
          rw [show (-(↑n + 1 : ℤ)) + (↑n + 1 : ℤ) = 0 by ring, zpow_zero]
        symm
        calc
          ‖P.q‖ ^ (-(↑n + 1 : ℤ)) * ‖(u.1 : K) - (v.1 : K)‖ *
              ‖P.q‖ ^ (↑n + 1 : ℤ) =
              (‖P.q‖ ^ (-(↑n + 1 : ℤ)) * ‖P.q‖ ^ (↑n + 1 : ℤ)) *
                ‖(u.1 : K) - (v.1 : K)‖ := by ring
          _ = 1 * ‖(u.1 : K) - (v.1 : K)‖ := by rw [hz]
          _ = ‖(u.1 : K) - (v.1 : K)‖ := by ring

end LeanFormal.IUT.XiFPaper.Mzk1P1NegativeTailActual
