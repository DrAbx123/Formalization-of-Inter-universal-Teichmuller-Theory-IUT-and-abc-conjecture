import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import tmp.sheaf.xif.paper.S2560S0ShiftedPartsActual
import tmp.sheaf.xif.paper.S2563R0LookupActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
open Polynomial

namespace LeanFormal.IUT.XiFPaper.Chain1Lt12Agent

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual
open LeanFormal.IUT.XiFPaper.S2563R0LookupActual

/-- For n < 12, the coefficient of G*P is the sum over the first n+1 coefficients of G.
(The -T1 side does not contribute since n < 613.) -/
lemma G_mul_coeff_lt (P : (ZMod 613)[X]) (n : ℕ) (_hn : n < 12) :
    (G * P).coeff n = ∑ a ∈ Finset.range (n + 1), G.coeff a * P.coeff (n - a) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

lemma S0_coeff_0 : S0.coeff 0 = 39 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_0]

lemma S0_coeff_1 : S0.coeff 1 = 281 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_1]

lemma S0_coeff_2 : S0.coeff 2 = 78 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_2]

lemma S0_coeff_3 : S0.coeff 3 = 265 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_3]

lemma S0_coeff_4 : S0.coeff 4 = 31 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_4]

lemma S0_coeff_5 : S0.coeff 5 = 121 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_5]

lemma S0_coeff_6 : S0.coeff 6 = 82 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_6]

lemma S0_coeff_7 : S0.coeff 7 = 150 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_7]

lemma S0_coeff_8 : S0.coeff 8 = 21 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_8]

lemma S0_coeff_9 : S0.coeff 9 = 336 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_9]

lemma S0_coeff_10 : S0.coeff 10 = 230 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_10]

lemma S0_coeff_11 : S0.coeff 11 = 554 := by
  rw [S0]
  simp [S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, R0_coeff_11]

lemma chain1_coeff_0 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 0 = (G * S0).coeff 0 := by
  rw [G_mul_coeff_lt S0 0 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_0]
  simp [G, T1]
  decide

lemma chain1_coeff_1 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 1 = (G * S0).coeff 1 := by
  rw [G_mul_coeff_lt S0 1 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_1, S0_coeff_0]
  simp [G, T1]
  decide

lemma chain1_coeff_2 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 2 = (G * S0).coeff 2 := by
  rw [G_mul_coeff_lt S0 2 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_2, S0_coeff_1, S0_coeff_0]
  simp [G, T1]
  decide

lemma chain1_coeff_3 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 3 = (G * S0).coeff 3 := by
  rw [G_mul_coeff_lt S0 3 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_3, S0_coeff_2, S0_coeff_1, S0_coeff_0]
  simp [G, T1]
  decide

lemma chain1_coeff_4 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 4 = (G * S0).coeff 4 := by
  rw [G_mul_coeff_lt S0 4 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_4, S0_coeff_3, S0_coeff_2, S0_coeff_1, S0_coeff_0]
  simp [G, T1]
  decide

lemma chain1_coeff_5 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 5 = (G * S0).coeff 5 := by
  rw [G_mul_coeff_lt S0 5 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_5, S0_coeff_4, S0_coeff_3, S0_coeff_2, S0_coeff_1, S0_coeff_0]
  simp [G, T1]
  decide

lemma chain1_coeff_6 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 6 = (G * S0).coeff 6 := by
  rw [G_mul_coeff_lt S0 6 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_6, S0_coeff_5, S0_coeff_4, S0_coeff_3, S0_coeff_2, S0_coeff_1, S0_coeff_0]
  simp [G, T1]
  decide

lemma chain1_coeff_7 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 7 = (G * S0).coeff 7 := by
  rw [G_mul_coeff_lt S0 7 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_7, S0_coeff_6, S0_coeff_5, S0_coeff_4, S0_coeff_3, S0_coeff_2, S0_coeff_1, S0_coeff_0]
  simp [G, T1]
  decide

lemma chain1_coeff_8 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 8 = (G * S0).coeff 8 := by
  rw [G_mul_coeff_lt S0 8 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_8, S0_coeff_7, S0_coeff_6, S0_coeff_5, S0_coeff_4, S0_coeff_3, S0_coeff_2, S0_coeff_1, S0_coeff_0]
  simp [G, T1]
  decide

lemma chain1_coeff_9 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 9 = (G * S0).coeff 9 := by
  rw [G_mul_coeff_lt S0 9 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_9, S0_coeff_8, S0_coeff_7, S0_coeff_6, S0_coeff_5, S0_coeff_4, S0_coeff_3, S0_coeff_2, S0_coeff_1, S0_coeff_0]
  simp [G, T1]
  decide

lemma chain1_coeff_10 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 10 = (G * S0).coeff 10 := by
  rw [G_mul_coeff_lt S0 10 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_10, S0_coeff_9, S0_coeff_8, S0_coeff_7, S0_coeff_6, S0_coeff_5, S0_coeff_4, S0_coeff_3, S0_coeff_2, S0_coeff_1, S0_coeff_0]
  simp [G, T1]
  decide

lemma chain1_coeff_11 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 11 = (G * S0).coeff 11 := by
  rw [G_mul_coeff_lt S0 11 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [S0_coeff_11, S0_coeff_10, S0_coeff_9, S0_coeff_8, S0_coeff_7, S0_coeff_6, S0_coeff_5, S0_coeff_4, S0_coeff_3, S0_coeff_2, S0_coeff_1, S0_coeff_0]
  simp [G, T1]
  decide

theorem chain1_coeff_lt12 (n : ℕ) (hn : n < 12) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff n = (G * S0).coeff n := by
  interval_cases n <;>
    simp only [chain1_coeff_0, chain1_coeff_1, chain1_coeff_2, chain1_coeff_3,
      chain1_coeff_4, chain1_coeff_5, chain1_coeff_6, chain1_coeff_7,
      chain1_coeff_8, chain1_coeff_9, chain1_coeff_10, chain1_coeff_11]

end LeanFormal.IUT.XiFPaper.Chain1Lt12Agent

end
