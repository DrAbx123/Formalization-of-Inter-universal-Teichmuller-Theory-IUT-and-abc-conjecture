/- U-C Step (ii)/(vi): hii、hsQ 与合并 hiii 的无条件纯实数显示引理。

IUT IV 原文:
* Step (ii) L1424-1433: (1+4/l) log dK <= (1+4/l) S_ar + 2 log l + 46;
* Step (vi) L1570-1577: (4/l) log s^Q <= (8 d_mod/l) S_ar + 6;
* 合并 L1578-1584: (1+4/l)log(dK) + (4/l)log(s^Q)
    <= (1+12 d_mod/l) S_ar + 2 log l + 52，用 d_mod >= 1（原文 L1584）。

本文件无 retained：输入只有上游界 hlogdK（paper Prop 1.3 链）、hsQ（实际 s^Q 小素数
估计，kurt urSQ/C1 权重）与 d_mod >= 1、S_ar >= 0（sophie 真证项）；常数核验全真证。 -/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import tmp.sheaf.xif.paper.Mzk1URSmallPrimeActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULStepHiiHsQActual

/-- l >= 5 时 20 + 4 log l <= 6 l（Step (vi) 常数 6）。
分两段: l <= 8 用 log 单调 + log 2 < 0.7; l >= 8 用 log l <= l - 1。 -/
theorem twenty_add_four_log_le_six_mul {l : ℝ} (hl : 5 ≤ l) :
    20 + 4 * Real.log l ≤ 6 * l := by
  have hlpos : 0 < l := by linarith
  by_cases h8 : l ≤ 8
  · have hlog : Real.log l ≤ Real.log 8 := Real.log_le_log hlpos h8
    have hlog8 : Real.log 8 ≤ 2.1 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      have h2 : Real.log 2 < 0.7 := by
        have := Real.log_two_lt_d9
        linarith
      nlinarith
    nlinarith
  · push Not at h8
    have hlog : Real.log l ≤ l - 1 := Real.log_le_sub_one_of_pos hlpos
    nlinarith

/-- **hii_arith**（IUT IV L1424-1433 Step (ii) 显示, 常数 46 核验, 无条件）:
由 log dK <= S_ar + 2 log l + 21 与 l >= 5 得 (1+4/l) log dK <= (1+4/l) S_ar + 2 log l + 46。 -/
theorem hii_arith {l logdK S_ar : ℝ} (hl : 5 ≤ l)
    (hlogdK : logdK ≤ S_ar + 2 * Real.log l + 21) :
    (1 + 4 / l) * logdK ≤ (1 + 4 / l) * S_ar + 2 * Real.log l + 46 := by
  have hlpos : 0 < l := by linarith
  have hlog : Real.log l ≤ l - 1 := Real.log_le_sub_one_of_pos hlpos
  have hmul : (1 + 4 / l) * logdK ≤ (1 + 4 / l) * (S_ar + 2 * Real.log l + 21) :=
    mul_le_mul_of_nonneg_left hlogdK (by positivity)
  have hB : (1 + 4 / l) * (S_ar + 2 * Real.log l + 21) ≤
      (1 + 4 / l) * S_ar + 2 * Real.log l + 46 := by
    field_simp
    nlinarith [hlog, hl]
  linarith

/-- **hsQ_arith**（IUT IV L1570-1577, 常数 6 核验, 无条件）:
由 log s^Q <= 2 d_mod S_ar + 5 + log l 与 l >= 5 得 (4/l) log s^Q <= (8 d_mod/l) S_ar + 6。 -/
theorem hsQ_arith {l logSQ d_mod S_ar : ℝ} (hl : 5 ≤ l)
    (hsQ : logSQ ≤ 2 * d_mod * S_ar + 5 + Real.log l) :
    (4 / l) * logSQ ≤ (8 * d_mod / l) * S_ar + 6 := by
  have hlpos : 0 < l := by linarith
  have hlog := twenty_add_four_log_le_six_mul hl
  have hmul : (4 / l) * logSQ ≤ (4 / l) * (2 * d_mod * S_ar + 5 + Real.log l) :=
    mul_le_mul_of_nonneg_left hsQ (by positivity)
  have hB : (4 / l) * (2 * d_mod * S_ar + 5 + Real.log l) ≤
      (8 * d_mod / l) * S_ar + 6 := by
    field_simp
    nlinarith [hlog, hl]
  linarith

/-- **hiii_arith**（IUT IV L1578-1584 合并显示, 无条件）:
hii + hsQ + d_mod >= 1 + S_ar >= 0
=> (1+4/l)log(dK) + (4/l)log(s^Q) <= (1+12 d_mod/l) S_ar + 2 log l + 52。 -/
theorem hiii_arith {l logdK logSQ d_mod S_ar : ℝ} (hl : 5 ≤ l)
    (hd_mod : 1 ≤ d_mod) (hS_ar : 0 ≤ S_ar)
    (hlogdK : logdK ≤ S_ar + 2 * Real.log l + 21)
    (hsQ : logSQ ≤ 2 * d_mod * S_ar + 5 + Real.log l) :
    (1 + 4 / l) * logdK + (4 / l) * logSQ ≤
      (1 + 12 * d_mod / l) * S_ar + 2 * Real.log l + 52 := by
  have hlpos : 0 < l := by linarith
  have h2 := hii_arith hl hlogdK
  have h6 := hsQ_arith hl hsQ
  have hcoef : (1 + 4 / l) + 8 * d_mod / l ≤ 1 + 12 * d_mod / l := by
    field_simp
    nlinarith [hd_mod]
  have hS := mul_le_mul_of_nonneg_right hcoef hS_ar
  have hsum : (1 + 4 / l) * logdK + (4 / l) * logSQ ≤
      ((1 + 4 / l) + 8 * d_mod / l) * S_ar + 2 * Real.log l + 52 := by
    have h : (1 + 4 / l) * S_ar + 2 * Real.log l + 46 + ((8 * d_mod / l) * S_ar + 6) =
        ((1 + 4 / l) + 8 * d_mod / l) * S_ar + 2 * Real.log l + 52 := by ring
    linarith
  linarith


/-! ## hsQraw 的小素数块: log(urSQ X) <= log(30*l) <= 5 + log l

论文 L1572 的 log(2·3·5·l) 部分; 数值核验用 log30 <= log32 = 5 log2 <= 5。
（urSQ_le 由 kurt 提供后，用 log 单调即得 log(urSQ X) <= 5+log l。） -/

/-- log 30 <= 5（30 < 32 = 2^5, log 2 <= 1）。 -/
theorem log_thirty_le_five : Real.log (30 : ℝ) ≤ 5 := by
  have h : Real.log (30 : ℝ) ≤ Real.log 32 := by
    apply Real.log_le_log (by norm_num)
    norm_num
  have h32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h32] at h
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  nlinarith [h2]

/-- log(30*l) <= 5 + log l（l > 0）。 -/
theorem log_thirty_mul_le {l : ℝ} (hl : 0 < l) :
    Real.log (30 * l) ≤ 5 + Real.log l := by
  rw [Real.log_mul (by norm_num) (ne_of_gt hl)]
  linarith [log_thirty_le_five]

/-- 小素数块: 0 < Y <= 30*l ⇒ log Y <= 5 + log l（kurt urSQ_le 的直接消费形状）。 -/
theorem log_le_five_add_log_of_le_thirty_mul {Y l : ℝ} (hY : 0 < Y) (hl : 0 < l)
    (hYX : Y ≤ 30 * l) :
    Real.log Y ≤ 5 + Real.log l := by
  have hmono : Real.log Y ≤ Real.log (30 * l) := Real.log_le_log hY hYX
  linarith [log_thirty_mul_le hl]

#print axioms log_thirty_le_five
#print axioms log_thirty_mul_le
#print axioms log_le_five_add_log_of_le_thirty_mul


/-! ## 与 kurt urSQ（DONE 19:00:00）的衔接: log(urSQ X) <= 5 + log l（小素数块） -/

/-- urSQ 的上界链: 若 urSQ X <= 30*l 且 l > 0，则 log(urSQ X) <= 5 + log l。
（kurt urSQ_le/urSQ_pos + log 单调 + log30 <= 5。） -/
theorem log_urSQ_le_thirty_mul {X : Nat} {l : Real} (hl : 0 < l)
    (hX : (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ X : Real) ≤ 30 * l) :
    Real.log (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ X : Real) ≤
      5 + Real.log l := by
  apply log_le_five_add_log_of_le_thirty_mul
  · exact_mod_cast LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ_pos X
  · exact hl
  · exact hX

#print axioms log_urSQ_le_thirty_mul

#print axioms twenty_add_four_log_le_six_mul
#print axioms hii_arith
#print axioms hsQ_arith
#print axioms hiii_arith

end LeanFormal.IUT.XiFPaper.Mzk1ULStepHiiHsQActual