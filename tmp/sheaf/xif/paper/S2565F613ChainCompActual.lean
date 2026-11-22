/-
S2565: F613 chain-1 coefficient computation (independent re-derivation).

Target, for k = 0 .. 11:
  ((X : (ZMod 613)[X]) ^ 613 - T1).coeff k = (G * S0).coeff k

Computed from the primary data only:
* S2554Mod613ChainDataActual: G, T1;
* S2560S0ShiftedPartsActual: R0..R7, S0_i, S0, S0_i_coeff;
* S2562GmulCoeffActual: G_mul_coeff_ge;
* S2563R0LookupActual: R0_coeff_0 .. R0_coeff_80.

Below degree 12, (G * S0).coeff k is the (k+1)-term support sum of G with
S0; the shifted pieces S0_1..S0_7 contribute nothing there, and the S0_0
coefficients are read off from R0 through the if-form S0_i_coeff lemmas
and the numeral lookups R0_coeff_j.

No axioms, no sorry, no native_decide.
-/

import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual
import tmp.sheaf.xif.paper.S2560S0ShiftedPartsActual
import tmp.sheaf.xif.paper.S2562GmulCoeffActual
import tmp.sheaf.xif.paper.S2563R0LookupActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2565F613ChainCompActual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2560S0ShiftedPartsActual
open LeanFormal.IUT.XiFPaper.S2562GmulCoeffActual
open LeanFormal.IUT.XiFPaper.S2563R0LookupActual

/-! ## Coefficient of X ^ 613 below its degree -/

lemma coeff_X_pow_613_of_lt (k : ℕ) (hk : k < 613) :
    ((X : (ZMod 613)[X]) ^ 613).coeff k = 0 := by
  rw [coeff_X_pow]
  simp [show k ≠ 613 by omega]

/-- The left-hand side below degree 613: only -T1 survives. -/
lemma lhs_coeff_of_lt (k : ℕ) (hk : k < 613) :
    ((X : (ZMod 613)[X]) ^ 613 - T1).coeff k = -T1.coeff k := by
  rw [coeff_sub, coeff_X_pow_613_of_lt k hk, zero_sub]

/-- T1 vanishes from degree 12 on. -/
lemma T1_coeff_eq_zero_of_ge_12 (k : ℕ) (hk : 12 ≤ k) : T1.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h : T1.natDegree ≤ 11 := by unfold T1; compute_degree!
  omega

/-- Below degree 12 the support sum has k + 1 genuine terms. -/
lemma G_mul_coeff_lt (P : (ZMod 613)[X]) (n : ℕ) (hn : n < 12) :
    (G * P).coeff n = ∑ a ∈ Finset.range (n + 1), G.coeff a * P.coeff (n - a) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

lemma chain1_coeff_0 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 0 = (G * S0).coeff 0 := by
  rw [lhs_coeff_of_lt 0 (by norm_num), G_mul_coeff_lt S0 0 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp [S0, S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, G, T1, R0_coeff_0, R0_coeff_1, R0_coeff_2, R0_coeff_3, R0_coeff_4, R0_coeff_5, R0_coeff_6, R0_coeff_7, R0_coeff_8, R0_coeff_9, R0_coeff_10, R0_coeff_11, R0_coeff_12, R0_coeff_13, R0_coeff_14, R0_coeff_15, R0_coeff_16, R0_coeff_17, R0_coeff_18, R0_coeff_19, R0_coeff_20, R0_coeff_21, R0_coeff_22, R0_coeff_23, R0_coeff_24, R0_coeff_25, R0_coeff_26, R0_coeff_27, R0_coeff_28, R0_coeff_29, R0_coeff_30, R0_coeff_31, R0_coeff_32, R0_coeff_33, R0_coeff_34, R0_coeff_35, R0_coeff_36, R0_coeff_37, R0_coeff_38, R0_coeff_39, R0_coeff_40, R0_coeff_41, R0_coeff_42, R0_coeff_43, R0_coeff_44, R0_coeff_45, R0_coeff_46, R0_coeff_47, R0_coeff_48, R0_coeff_49, R0_coeff_50, R0_coeff_51, R0_coeff_52, R0_coeff_53, R0_coeff_54, R0_coeff_55, R0_coeff_56, R0_coeff_57, R0_coeff_58, R0_coeff_59, R0_coeff_60, R0_coeff_61, R0_coeff_62, R0_coeff_63, R0_coeff_64, R0_coeff_65, R0_coeff_66, R0_coeff_67, R0_coeff_68, R0_coeff_69, R0_coeff_70, R0_coeff_71, R0_coeff_72, R0_coeff_73, R0_coeff_74, R0_coeff_75, R0_coeff_76, R0_coeff_77, R0_coeff_78, R0_coeff_79, R0_coeff_80] <;> decide

lemma chain1_coeff_1 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 1 = (G * S0).coeff 1 := by
  rw [lhs_coeff_of_lt 1 (by norm_num), G_mul_coeff_lt S0 1 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp [S0, S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, G, T1, R0_coeff_0, R0_coeff_1, R0_coeff_2, R0_coeff_3, R0_coeff_4, R0_coeff_5, R0_coeff_6, R0_coeff_7, R0_coeff_8, R0_coeff_9, R0_coeff_10, R0_coeff_11, R0_coeff_12, R0_coeff_13, R0_coeff_14, R0_coeff_15, R0_coeff_16, R0_coeff_17, R0_coeff_18, R0_coeff_19, R0_coeff_20, R0_coeff_21, R0_coeff_22, R0_coeff_23, R0_coeff_24, R0_coeff_25, R0_coeff_26, R0_coeff_27, R0_coeff_28, R0_coeff_29, R0_coeff_30, R0_coeff_31, R0_coeff_32, R0_coeff_33, R0_coeff_34, R0_coeff_35, R0_coeff_36, R0_coeff_37, R0_coeff_38, R0_coeff_39, R0_coeff_40, R0_coeff_41, R0_coeff_42, R0_coeff_43, R0_coeff_44, R0_coeff_45, R0_coeff_46, R0_coeff_47, R0_coeff_48, R0_coeff_49, R0_coeff_50, R0_coeff_51, R0_coeff_52, R0_coeff_53, R0_coeff_54, R0_coeff_55, R0_coeff_56, R0_coeff_57, R0_coeff_58, R0_coeff_59, R0_coeff_60, R0_coeff_61, R0_coeff_62, R0_coeff_63, R0_coeff_64, R0_coeff_65, R0_coeff_66, R0_coeff_67, R0_coeff_68, R0_coeff_69, R0_coeff_70, R0_coeff_71, R0_coeff_72, R0_coeff_73, R0_coeff_74, R0_coeff_75, R0_coeff_76, R0_coeff_77, R0_coeff_78, R0_coeff_79, R0_coeff_80] <;> decide

lemma chain1_coeff_2 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 2 = (G * S0).coeff 2 := by
  rw [lhs_coeff_of_lt 2 (by norm_num), G_mul_coeff_lt S0 2 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp [S0, S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, G, T1, R0_coeff_0, R0_coeff_1, R0_coeff_2, R0_coeff_3, R0_coeff_4, R0_coeff_5, R0_coeff_6, R0_coeff_7, R0_coeff_8, R0_coeff_9, R0_coeff_10, R0_coeff_11, R0_coeff_12, R0_coeff_13, R0_coeff_14, R0_coeff_15, R0_coeff_16, R0_coeff_17, R0_coeff_18, R0_coeff_19, R0_coeff_20, R0_coeff_21, R0_coeff_22, R0_coeff_23, R0_coeff_24, R0_coeff_25, R0_coeff_26, R0_coeff_27, R0_coeff_28, R0_coeff_29, R0_coeff_30, R0_coeff_31, R0_coeff_32, R0_coeff_33, R0_coeff_34, R0_coeff_35, R0_coeff_36, R0_coeff_37, R0_coeff_38, R0_coeff_39, R0_coeff_40, R0_coeff_41, R0_coeff_42, R0_coeff_43, R0_coeff_44, R0_coeff_45, R0_coeff_46, R0_coeff_47, R0_coeff_48, R0_coeff_49, R0_coeff_50, R0_coeff_51, R0_coeff_52, R0_coeff_53, R0_coeff_54, R0_coeff_55, R0_coeff_56, R0_coeff_57, R0_coeff_58, R0_coeff_59, R0_coeff_60, R0_coeff_61, R0_coeff_62, R0_coeff_63, R0_coeff_64, R0_coeff_65, R0_coeff_66, R0_coeff_67, R0_coeff_68, R0_coeff_69, R0_coeff_70, R0_coeff_71, R0_coeff_72, R0_coeff_73, R0_coeff_74, R0_coeff_75, R0_coeff_76, R0_coeff_77, R0_coeff_78, R0_coeff_79, R0_coeff_80] <;> decide

lemma chain1_coeff_3 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 3 = (G * S0).coeff 3 := by
  rw [lhs_coeff_of_lt 3 (by norm_num), G_mul_coeff_lt S0 3 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp [S0, S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, G, T1, R0_coeff_0, R0_coeff_1, R0_coeff_2, R0_coeff_3, R0_coeff_4, R0_coeff_5, R0_coeff_6, R0_coeff_7, R0_coeff_8, R0_coeff_9, R0_coeff_10, R0_coeff_11, R0_coeff_12, R0_coeff_13, R0_coeff_14, R0_coeff_15, R0_coeff_16, R0_coeff_17, R0_coeff_18, R0_coeff_19, R0_coeff_20, R0_coeff_21, R0_coeff_22, R0_coeff_23, R0_coeff_24, R0_coeff_25, R0_coeff_26, R0_coeff_27, R0_coeff_28, R0_coeff_29, R0_coeff_30, R0_coeff_31, R0_coeff_32, R0_coeff_33, R0_coeff_34, R0_coeff_35, R0_coeff_36, R0_coeff_37, R0_coeff_38, R0_coeff_39, R0_coeff_40, R0_coeff_41, R0_coeff_42, R0_coeff_43, R0_coeff_44, R0_coeff_45, R0_coeff_46, R0_coeff_47, R0_coeff_48, R0_coeff_49, R0_coeff_50, R0_coeff_51, R0_coeff_52, R0_coeff_53, R0_coeff_54, R0_coeff_55, R0_coeff_56, R0_coeff_57, R0_coeff_58, R0_coeff_59, R0_coeff_60, R0_coeff_61, R0_coeff_62, R0_coeff_63, R0_coeff_64, R0_coeff_65, R0_coeff_66, R0_coeff_67, R0_coeff_68, R0_coeff_69, R0_coeff_70, R0_coeff_71, R0_coeff_72, R0_coeff_73, R0_coeff_74, R0_coeff_75, R0_coeff_76, R0_coeff_77, R0_coeff_78, R0_coeff_79, R0_coeff_80] <;> decide

lemma chain1_coeff_4 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 4 = (G * S0).coeff 4 := by
  rw [lhs_coeff_of_lt 4 (by norm_num), G_mul_coeff_lt S0 4 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp [S0, S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, G, T1, R0_coeff_0, R0_coeff_1, R0_coeff_2, R0_coeff_3, R0_coeff_4, R0_coeff_5, R0_coeff_6, R0_coeff_7, R0_coeff_8, R0_coeff_9, R0_coeff_10, R0_coeff_11, R0_coeff_12, R0_coeff_13, R0_coeff_14, R0_coeff_15, R0_coeff_16, R0_coeff_17, R0_coeff_18, R0_coeff_19, R0_coeff_20, R0_coeff_21, R0_coeff_22, R0_coeff_23, R0_coeff_24, R0_coeff_25, R0_coeff_26, R0_coeff_27, R0_coeff_28, R0_coeff_29, R0_coeff_30, R0_coeff_31, R0_coeff_32, R0_coeff_33, R0_coeff_34, R0_coeff_35, R0_coeff_36, R0_coeff_37, R0_coeff_38, R0_coeff_39, R0_coeff_40, R0_coeff_41, R0_coeff_42, R0_coeff_43, R0_coeff_44, R0_coeff_45, R0_coeff_46, R0_coeff_47, R0_coeff_48, R0_coeff_49, R0_coeff_50, R0_coeff_51, R0_coeff_52, R0_coeff_53, R0_coeff_54, R0_coeff_55, R0_coeff_56, R0_coeff_57, R0_coeff_58, R0_coeff_59, R0_coeff_60, R0_coeff_61, R0_coeff_62, R0_coeff_63, R0_coeff_64, R0_coeff_65, R0_coeff_66, R0_coeff_67, R0_coeff_68, R0_coeff_69, R0_coeff_70, R0_coeff_71, R0_coeff_72, R0_coeff_73, R0_coeff_74, R0_coeff_75, R0_coeff_76, R0_coeff_77, R0_coeff_78, R0_coeff_79, R0_coeff_80] <;> decide

lemma chain1_coeff_5 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 5 = (G * S0).coeff 5 := by
  rw [lhs_coeff_of_lt 5 (by norm_num), G_mul_coeff_lt S0 5 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp [S0, S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, G, T1, R0_coeff_0, R0_coeff_1, R0_coeff_2, R0_coeff_3, R0_coeff_4, R0_coeff_5, R0_coeff_6, R0_coeff_7, R0_coeff_8, R0_coeff_9, R0_coeff_10, R0_coeff_11, R0_coeff_12, R0_coeff_13, R0_coeff_14, R0_coeff_15, R0_coeff_16, R0_coeff_17, R0_coeff_18, R0_coeff_19, R0_coeff_20, R0_coeff_21, R0_coeff_22, R0_coeff_23, R0_coeff_24, R0_coeff_25, R0_coeff_26, R0_coeff_27, R0_coeff_28, R0_coeff_29, R0_coeff_30, R0_coeff_31, R0_coeff_32, R0_coeff_33, R0_coeff_34, R0_coeff_35, R0_coeff_36, R0_coeff_37, R0_coeff_38, R0_coeff_39, R0_coeff_40, R0_coeff_41, R0_coeff_42, R0_coeff_43, R0_coeff_44, R0_coeff_45, R0_coeff_46, R0_coeff_47, R0_coeff_48, R0_coeff_49, R0_coeff_50, R0_coeff_51, R0_coeff_52, R0_coeff_53, R0_coeff_54, R0_coeff_55, R0_coeff_56, R0_coeff_57, R0_coeff_58, R0_coeff_59, R0_coeff_60, R0_coeff_61, R0_coeff_62, R0_coeff_63, R0_coeff_64, R0_coeff_65, R0_coeff_66, R0_coeff_67, R0_coeff_68, R0_coeff_69, R0_coeff_70, R0_coeff_71, R0_coeff_72, R0_coeff_73, R0_coeff_74, R0_coeff_75, R0_coeff_76, R0_coeff_77, R0_coeff_78, R0_coeff_79, R0_coeff_80] <;> decide

lemma chain1_coeff_6 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 6 = (G * S0).coeff 6 := by
  rw [lhs_coeff_of_lt 6 (by norm_num), G_mul_coeff_lt S0 6 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp [S0, S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, G, T1, R0_coeff_0, R0_coeff_1, R0_coeff_2, R0_coeff_3, R0_coeff_4, R0_coeff_5, R0_coeff_6, R0_coeff_7, R0_coeff_8, R0_coeff_9, R0_coeff_10, R0_coeff_11, R0_coeff_12, R0_coeff_13, R0_coeff_14, R0_coeff_15, R0_coeff_16, R0_coeff_17, R0_coeff_18, R0_coeff_19, R0_coeff_20, R0_coeff_21, R0_coeff_22, R0_coeff_23, R0_coeff_24, R0_coeff_25, R0_coeff_26, R0_coeff_27, R0_coeff_28, R0_coeff_29, R0_coeff_30, R0_coeff_31, R0_coeff_32, R0_coeff_33, R0_coeff_34, R0_coeff_35, R0_coeff_36, R0_coeff_37, R0_coeff_38, R0_coeff_39, R0_coeff_40, R0_coeff_41, R0_coeff_42, R0_coeff_43, R0_coeff_44, R0_coeff_45, R0_coeff_46, R0_coeff_47, R0_coeff_48, R0_coeff_49, R0_coeff_50, R0_coeff_51, R0_coeff_52, R0_coeff_53, R0_coeff_54, R0_coeff_55, R0_coeff_56, R0_coeff_57, R0_coeff_58, R0_coeff_59, R0_coeff_60, R0_coeff_61, R0_coeff_62, R0_coeff_63, R0_coeff_64, R0_coeff_65, R0_coeff_66, R0_coeff_67, R0_coeff_68, R0_coeff_69, R0_coeff_70, R0_coeff_71, R0_coeff_72, R0_coeff_73, R0_coeff_74, R0_coeff_75, R0_coeff_76, R0_coeff_77, R0_coeff_78, R0_coeff_79, R0_coeff_80] <;> decide

lemma chain1_coeff_7 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 7 = (G * S0).coeff 7 := by
  rw [lhs_coeff_of_lt 7 (by norm_num), G_mul_coeff_lt S0 7 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp [S0, S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, G, T1, R0_coeff_0, R0_coeff_1, R0_coeff_2, R0_coeff_3, R0_coeff_4, R0_coeff_5, R0_coeff_6, R0_coeff_7, R0_coeff_8, R0_coeff_9, R0_coeff_10, R0_coeff_11, R0_coeff_12, R0_coeff_13, R0_coeff_14, R0_coeff_15, R0_coeff_16, R0_coeff_17, R0_coeff_18, R0_coeff_19, R0_coeff_20, R0_coeff_21, R0_coeff_22, R0_coeff_23, R0_coeff_24, R0_coeff_25, R0_coeff_26, R0_coeff_27, R0_coeff_28, R0_coeff_29, R0_coeff_30, R0_coeff_31, R0_coeff_32, R0_coeff_33, R0_coeff_34, R0_coeff_35, R0_coeff_36, R0_coeff_37, R0_coeff_38, R0_coeff_39, R0_coeff_40, R0_coeff_41, R0_coeff_42, R0_coeff_43, R0_coeff_44, R0_coeff_45, R0_coeff_46, R0_coeff_47, R0_coeff_48, R0_coeff_49, R0_coeff_50, R0_coeff_51, R0_coeff_52, R0_coeff_53, R0_coeff_54, R0_coeff_55, R0_coeff_56, R0_coeff_57, R0_coeff_58, R0_coeff_59, R0_coeff_60, R0_coeff_61, R0_coeff_62, R0_coeff_63, R0_coeff_64, R0_coeff_65, R0_coeff_66, R0_coeff_67, R0_coeff_68, R0_coeff_69, R0_coeff_70, R0_coeff_71, R0_coeff_72, R0_coeff_73, R0_coeff_74, R0_coeff_75, R0_coeff_76, R0_coeff_77, R0_coeff_78, R0_coeff_79, R0_coeff_80] <;> decide

lemma chain1_coeff_8 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 8 = (G * S0).coeff 8 := by
  rw [lhs_coeff_of_lt 8 (by norm_num), G_mul_coeff_lt S0 8 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp [S0, S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, G, T1, R0_coeff_0, R0_coeff_1, R0_coeff_2, R0_coeff_3, R0_coeff_4, R0_coeff_5, R0_coeff_6, R0_coeff_7, R0_coeff_8, R0_coeff_9, R0_coeff_10, R0_coeff_11, R0_coeff_12, R0_coeff_13, R0_coeff_14, R0_coeff_15, R0_coeff_16, R0_coeff_17, R0_coeff_18, R0_coeff_19, R0_coeff_20, R0_coeff_21, R0_coeff_22, R0_coeff_23, R0_coeff_24, R0_coeff_25, R0_coeff_26, R0_coeff_27, R0_coeff_28, R0_coeff_29, R0_coeff_30, R0_coeff_31, R0_coeff_32, R0_coeff_33, R0_coeff_34, R0_coeff_35, R0_coeff_36, R0_coeff_37, R0_coeff_38, R0_coeff_39, R0_coeff_40, R0_coeff_41, R0_coeff_42, R0_coeff_43, R0_coeff_44, R0_coeff_45, R0_coeff_46, R0_coeff_47, R0_coeff_48, R0_coeff_49, R0_coeff_50, R0_coeff_51, R0_coeff_52, R0_coeff_53, R0_coeff_54, R0_coeff_55, R0_coeff_56, R0_coeff_57, R0_coeff_58, R0_coeff_59, R0_coeff_60, R0_coeff_61, R0_coeff_62, R0_coeff_63, R0_coeff_64, R0_coeff_65, R0_coeff_66, R0_coeff_67, R0_coeff_68, R0_coeff_69, R0_coeff_70, R0_coeff_71, R0_coeff_72, R0_coeff_73, R0_coeff_74, R0_coeff_75, R0_coeff_76, R0_coeff_77, R0_coeff_78, R0_coeff_79, R0_coeff_80] <;> decide

lemma chain1_coeff_9 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 9 = (G * S0).coeff 9 := by
  rw [lhs_coeff_of_lt 9 (by norm_num), G_mul_coeff_lt S0 9 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp [S0, S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, G, T1, R0_coeff_0, R0_coeff_1, R0_coeff_2, R0_coeff_3, R0_coeff_4, R0_coeff_5, R0_coeff_6, R0_coeff_7, R0_coeff_8, R0_coeff_9, R0_coeff_10, R0_coeff_11, R0_coeff_12, R0_coeff_13, R0_coeff_14, R0_coeff_15, R0_coeff_16, R0_coeff_17, R0_coeff_18, R0_coeff_19, R0_coeff_20, R0_coeff_21, R0_coeff_22, R0_coeff_23, R0_coeff_24, R0_coeff_25, R0_coeff_26, R0_coeff_27, R0_coeff_28, R0_coeff_29, R0_coeff_30, R0_coeff_31, R0_coeff_32, R0_coeff_33, R0_coeff_34, R0_coeff_35, R0_coeff_36, R0_coeff_37, R0_coeff_38, R0_coeff_39, R0_coeff_40, R0_coeff_41, R0_coeff_42, R0_coeff_43, R0_coeff_44, R0_coeff_45, R0_coeff_46, R0_coeff_47, R0_coeff_48, R0_coeff_49, R0_coeff_50, R0_coeff_51, R0_coeff_52, R0_coeff_53, R0_coeff_54, R0_coeff_55, R0_coeff_56, R0_coeff_57, R0_coeff_58, R0_coeff_59, R0_coeff_60, R0_coeff_61, R0_coeff_62, R0_coeff_63, R0_coeff_64, R0_coeff_65, R0_coeff_66, R0_coeff_67, R0_coeff_68, R0_coeff_69, R0_coeff_70, R0_coeff_71, R0_coeff_72, R0_coeff_73, R0_coeff_74, R0_coeff_75, R0_coeff_76, R0_coeff_77, R0_coeff_78, R0_coeff_79, R0_coeff_80] <;> decide

lemma chain1_coeff_10 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 10 = (G * S0).coeff 10 := by
  rw [lhs_coeff_of_lt 10 (by norm_num), G_mul_coeff_lt S0 10 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp [S0, S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, G, T1, R0_coeff_0, R0_coeff_1, R0_coeff_2, R0_coeff_3, R0_coeff_4, R0_coeff_5, R0_coeff_6, R0_coeff_7, R0_coeff_8, R0_coeff_9, R0_coeff_10, R0_coeff_11, R0_coeff_12, R0_coeff_13, R0_coeff_14, R0_coeff_15, R0_coeff_16, R0_coeff_17, R0_coeff_18, R0_coeff_19, R0_coeff_20, R0_coeff_21, R0_coeff_22, R0_coeff_23, R0_coeff_24, R0_coeff_25, R0_coeff_26, R0_coeff_27, R0_coeff_28, R0_coeff_29, R0_coeff_30, R0_coeff_31, R0_coeff_32, R0_coeff_33, R0_coeff_34, R0_coeff_35, R0_coeff_36, R0_coeff_37, R0_coeff_38, R0_coeff_39, R0_coeff_40, R0_coeff_41, R0_coeff_42, R0_coeff_43, R0_coeff_44, R0_coeff_45, R0_coeff_46, R0_coeff_47, R0_coeff_48, R0_coeff_49, R0_coeff_50, R0_coeff_51, R0_coeff_52, R0_coeff_53, R0_coeff_54, R0_coeff_55, R0_coeff_56, R0_coeff_57, R0_coeff_58, R0_coeff_59, R0_coeff_60, R0_coeff_61, R0_coeff_62, R0_coeff_63, R0_coeff_64, R0_coeff_65, R0_coeff_66, R0_coeff_67, R0_coeff_68, R0_coeff_69, R0_coeff_70, R0_coeff_71, R0_coeff_72, R0_coeff_73, R0_coeff_74, R0_coeff_75, R0_coeff_76, R0_coeff_77, R0_coeff_78, R0_coeff_79, R0_coeff_80] <;> decide

lemma chain1_coeff_11 : ((X : (ZMod 613)[X]) ^ 613 - T1).coeff 11 = (G * S0).coeff 11 := by
  rw [lhs_coeff_of_lt 11 (by norm_num), G_mul_coeff_lt S0 11 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp [S0, S0_0_coeff, S0_1_coeff, S0_2_coeff, S0_3_coeff, S0_4_coeff, S0_5_coeff, S0_6_coeff, S0_7_coeff, G, T1, R0_coeff_0, R0_coeff_1, R0_coeff_2, R0_coeff_3, R0_coeff_4, R0_coeff_5, R0_coeff_6, R0_coeff_7, R0_coeff_8, R0_coeff_9, R0_coeff_10, R0_coeff_11, R0_coeff_12, R0_coeff_13, R0_coeff_14, R0_coeff_15, R0_coeff_16, R0_coeff_17, R0_coeff_18, R0_coeff_19, R0_coeff_20, R0_coeff_21, R0_coeff_22, R0_coeff_23, R0_coeff_24, R0_coeff_25, R0_coeff_26, R0_coeff_27, R0_coeff_28, R0_coeff_29, R0_coeff_30, R0_coeff_31, R0_coeff_32, R0_coeff_33, R0_coeff_34, R0_coeff_35, R0_coeff_36, R0_coeff_37, R0_coeff_38, R0_coeff_39, R0_coeff_40, R0_coeff_41, R0_coeff_42, R0_coeff_43, R0_coeff_44, R0_coeff_45, R0_coeff_46, R0_coeff_47, R0_coeff_48, R0_coeff_49, R0_coeff_50, R0_coeff_51, R0_coeff_52, R0_coeff_53, R0_coeff_54, R0_coeff_55, R0_coeff_56, R0_coeff_57, R0_coeff_58, R0_coeff_59, R0_coeff_60, R0_coeff_61, R0_coeff_62, R0_coeff_63, R0_coeff_64, R0_coeff_65, R0_coeff_66, R0_coeff_67, R0_coeff_68, R0_coeff_69, R0_coeff_70, R0_coeff_71, R0_coeff_72, R0_coeff_73, R0_coeff_74, R0_coeff_75, R0_coeff_76, R0_coeff_77, R0_coeff_78, R0_coeff_79, R0_coeff_80] <;> decide

end LeanFormal.IUT.XiFPaper.S2565F613ChainCompActual

end
