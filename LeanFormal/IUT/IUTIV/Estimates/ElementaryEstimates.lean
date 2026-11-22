/-
# IUT IV Thm 1.10 证明内初等核算 (E1)–(E6) 落点

论文出处（行号均为 `papers\motizuki_corpus\text\Inter-universal Teichmuller Theory IV.txt` 的行）：
定理 1.10 证明 (i) 段（L1386–1407）"elementary identities / elementary facts"：
- (E1) L1387–1392：(1/n)·Σ_{m=1}^{n} m = (1/2)(n+1)（n ∈ N≥1）；
- (E2) L1393–1398：(1/n)·Σ_{m=1}^{n} m² = (1/6)(2n+1)(n+1)；
- (E3) L1402–1403：|GL2(F_p)| = p(p+1)(p−1)²（p 素数）；
- (E4) L1404–1405：p = 2,3,5 的数值化；
- (E5) L1406：扩域 F_mod(√−1)/F_mod 的次数 ≤ 2；
- (E6) L1407：0 ≤ log(2) ≤ 1, 1 ≤ log(3) ≤ log(π) ≤ log(5) ≤ 2。

消费者：Thm 1.10 证明 (ii) 段（L1412–1421）在素数 2·3·5 处联合使用
"Proposition 1.3, (ii), together with (E3), (E4), (E5), (E6)"（L1416–1417）；
(E1)/(E2) 供 C_Θ 取法的平均型常数核算（L1363–1384）。

缩减显式标注（相对原文）：
- (E1)/(E2)：原文 n ∈ N≥1；本文件对 n : ℕ 以 1 ≤ n 陈述 ℝ 等式，求和区间取 `Finset.Icc 1 n`。
  辅助引理 `sum_Icc_one_cast` / `sum_Icc_one_sq_cast` 对全部 n 成立（n = 0 时区间空、和为 0）。
- (E3)：|GL2(F_p)| 形式化为 `Nat.card (GL (Fin 2) (ZMod p))`；计数经 Mathlib
  `Matrix.card_GL_field`（= ∏_{i : Fin 2}(p² − p^i)）与 `ZMod.card` 落地。
- (E4)：原文 OCR 丢失上标（"3·24"、"5·25·3"）；按数值核验还原为 3·2⁴ = 48 与 5·2⁵·3 = 480，
  与 (E3) 在 p = 3, 5 的值一致。
- (E5)：形式化为一般形态"含 x（x² = −1）的域扩张 E/F 上 F⟮x⟯/F 的次数 ≤ 2"；
  F_mod 情形为其实例（不假设 √−1 ∈ F_mod；若已在，则次数为 1，仍 ≤ 2）。
- (E6)：以 ℝ 上六项合取陈述；逐项由 Mathlib 界（log_nonneg、log_le_sub_one_of_pos、
  le_log_iff_exp_le、exp_one_lt_three、pi_gt_three、pi_lt_four、log_five_lt_d9）给出。
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Polynomial

namespace LeanFormal.IUT.IUTIV.Estimates

/-- (E1)/(E2) 辅助：Icc 1 n 上的一次和（对全部 n；n = 0 时为 0）。 -/
lemma sum_Icc_one_cast (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 n, (m : ℝ)) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero =>
    rw [Finset.Icc_eq_empty_of_lt (show (0 : ℕ) < 1 by norm_num), Finset.sum_empty]
    norm_num
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ k + 1 by omega) (fun m : ℕ => (m : ℝ)), ih]
    push_cast
    ring

/-- (E1)/(E2) 辅助：Icc 1 n 上的平方和（对全部 n；n = 0 时为 0）。 -/
lemma sum_Icc_one_sq_cast (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 n, (m : ℝ) ^ 2) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by
  induction n with
  | zero =>
    rw [Finset.Icc_eq_empty_of_lt (show (0 : ℕ) < 1 by norm_num), Finset.sum_empty]
    norm_num
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ k + 1 by omega) (fun m : ℕ => (m : ℝ) ^ 2), ih]
    push_cast
    ring

/-- (E1)（L1387–1392）：n ≥ 1 时 (1/n)·Σ_{m=1}^{n} m = (n+1)/2。 -/
theorem iutIVThm110_e1_arithmeticMean (n : ℕ) (hn : 1 ≤ n) :
    (1 / (n : ℝ)) * (∑ m ∈ Finset.Icc 1 n, (m : ℝ)) = ((n : ℝ) + 1) / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    exact this.ne'
  rw [sum_Icc_one_cast n]
  calc (1 / (n : ℝ)) * ((n : ℝ) * ((n : ℝ) + 1) / 2)
      = ((n : ℝ) / (n : ℝ)) * (((n : ℝ) + 1) / 2) := by ring
    _ = 1 * (((n : ℝ) + 1) / 2) := by rw [div_self hn0]
    _ = ((n : ℝ) + 1) / 2 := one_mul _

/-- (E2)（L1393–1398）：n ≥ 1 时 (1/n)·Σ_{m=1}^{n} m² = (1/6)(2n+1)(n+1)。 -/
theorem iutIVThm110_e2_arithmeticMeanSquares (n : ℕ) (hn : 1 ≤ n) :
    (1 / (n : ℝ)) * (∑ m ∈ Finset.Icc 1 n, (m : ℝ) ^ 2) =
      (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / 6 := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    exact this.ne'
  rw [sum_Icc_one_sq_cast n]
  calc (1 / (n : ℝ)) * ((n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6)
      = ((n : ℝ) / (n : ℝ)) * (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6) := by ring
    _ = 1 * (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6) := by rw [div_self hn0]
    _ = (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) / 6 := by ring

/-- (E3)（L1402–1403）：p 素数 ⇒ |GL2(F_p)| = p(p+1)(p−1)²。 -/
theorem iutIVThm110_e3_card_GL2_modPrime (p : ℕ) (hp : p.Prime) :
    Nat.card (GL (Fin 2) (ZMod p)) = p * (p + 1) * (p - 1) ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [Matrix.card_GL_field 2, Fin.prod_univ_two, ZMod.card]
  change (p ^ 2 - p ^ ((0 : Fin 2) : ℕ)) * (p ^ 2 - p ^ ((1 : Fin 2) : ℕ)) =
    p * (p + 1) * (p - 1) ^ 2
  have hf0 : ((0 : Fin 2) : ℕ) = 0 := by decide
  have hf1 : ((1 : Fin 2) : ℕ) = 1 := by decide
  rw [hf0, hf1, pow_zero, pow_one]
  have h1 : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have h := sq_tsub_sq p 1
    rw [one_pow] at h
    exact h.trans (mul_comm (p + 1) (p - 1))
  have h2 : p ^ 2 - p = p * (p - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib, mul_one]
  rw [h1, h2]
  ring

/-- (E4)（L1404–1405）：p = 2,3,5 的数值核算（上标按数值核验还原：3·2⁴ = 48、5·2⁵·3 = 480）。 -/
theorem iutIVThm110_e4_card_GL2_smallPrimes :
    (2 * (2 + 1) * (2 - 1) ^ 2 : ℕ) = 2 * 3 ∧
    (3 * (3 + 1) * (3 - 1) ^ 2 : ℕ) = 3 * 2 ^ 4 ∧
    (5 * (5 + 1) * (5 - 1) ^ 2 : ℕ) = 5 * 2 ^ 5 * 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- (E5)（L1406）：含 x（x² = −1）的域扩张上 F⟮x⟯/F 的次数 ≤ 2。 -/
theorem iutIVThm110_e5_adjoin_sqrtNegOne_finrank_le_two
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : E) (hx : x ^ 2 = -1) :
    Module.finrank F (IntermediateField.adjoin F {x}) ≤ 2 := by
  have hroot : Polynomial.aeval x (X ^ 2 + C 1 : Polynomial F) = 0 := by
    rw [Polynomial.aeval_add, Polynomial.aeval_X_pow, Polynomial.aeval_C, hx]
    simp
  have hint : IsIntegral F x :=
    ⟨X ^ 2 + C 1, monic_X_pow_add_C (1 : F) (by norm_num : (2 : ℕ) ≠ 0),
      by rw [← Polynomial.aeval_def]; exact hroot⟩
  rw [IntermediateField.adjoin.finrank hint]
  calc (minpoly F x).natDegree
      ≤ (X ^ 2 + C 1 : Polynomial F).natDegree :=
        Polynomial.natDegree_le_of_dvd (minpoly.dvd F x hroot)
          (monic_X_pow_add_C (1 : F) (by norm_num : (2 : ℕ) ≠ 0)).ne_zero
    _ = 2 := Polynomial.natDegree_X_pow_add_C

/-- (E6)（L1407）：0 ≤ log 2 ≤ 1, 1 ≤ log 3 ≤ log π ≤ log 5 ≤ 2。 -/
theorem iutIVThm110_e6_logBounds :
    (0 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 ∧
    (1 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ Real.log Real.pi ∧
    Real.log Real.pi ≤ Real.log 5 ∧ Real.log 5 ≤ 2 := by
  refine ⟨Real.log_nonneg (by norm_num), ?_, ?_, ?_, ?_, ?_⟩
  · linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  · exact (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)).mpr
      (le_of_lt Real.exp_one_lt_three)
  · exact Real.log_le_log (by norm_num : (0 : ℝ) < 3) (le_of_lt Real.pi_gt_three)
  · exact Real.log_le_log Real.pi_pos
      (le_of_lt (Real.pi_lt_four.trans_le (by norm_num : (4 : ℝ) ≤ 5)))
  · linarith [Real.log_five_lt_d9]

end LeanFormal.IUT.IUTIV.Estimates
