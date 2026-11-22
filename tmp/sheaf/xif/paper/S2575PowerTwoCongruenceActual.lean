import tmp.sheaf.xif.paper.S2560Batch1Actual

noncomputable section
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1Actual

namespace LeanFormal.IUT.XiFPaper.S2575PowerTwoCongruenceActual

def Q0 : (ZMod 1249)[X] := 0
def Q1 : (ZMod 1249)[X] := 0
def Q2 : (ZMod 1249)[X] := 0
def Q3 : (ZMod 1249)[X] := 823 + X * 588 + X ^ 2 * 967 + X ^ 3 * 13 + X ^ 4 * 592 + X ^ 5 * 679 + X ^ 6 * 1
def Q4 : (ZMod 1249)[X] := 867 + X * 15 + X ^ 2 * 760 + X ^ 3 * 406 + X ^ 4 * 464 + X ^ 5 * 255 + X ^ 6 * 972 + X ^ 7 * 229 + X ^ 8 * 1159
def Q5 : (ZMod 1249)[X] := 285 + X * 138 + X ^ 2 * 1169 + X ^ 3 * 1206 + X ^ 4 * 296 + X ^ 5 * 375 + X ^ 6 * 40 + X ^ 7 * 647 + X ^ 8 * 483
def Q6 : (ZMod 1249)[X] := 766 + X * 244 + X ^ 2 * 926 + X ^ 3 * 359 + X ^ 4 * 316 + X ^ 5 * 44 + X ^ 6 * 318 + X ^ 7 * 200 + X ^ 8 * 857
def Q7 : (ZMod 1249)[X] := 1215 + X * 1239 + X ^ 2 * 880 + X ^ 3 * 1214 + X ^ 4 * 1061 + X ^ 5 * 617 + X ^ 6 * 109 + X ^ 7 * 50 + X ^ 8 * 51
def Q8 : (ZMod 1249)[X] := 783 + X * 889 + X ^ 2 * 1053 + X ^ 3 * 676 + X ^ 4 * 1213 + X ^ 5 * 339 + X ^ 6 * 821 + X ^ 7 * 818 + X ^ 8 * 877
def Q9 : (ZMod 1249)[X] := 237 + X * 1001 + X ^ 2 * 601 + X ^ 3 * 854 + X ^ 4 * 787 + X ^ 5 * 445 + X ^ 6 * 266 + X ^ 7 * 728 + X ^ 8 * 664

lemma pow_two_succ (k : ℕ) : (X : (ZMod 1249)[X]) ^ (2 ^ (k + 1)) = (X ^ (2 ^ k)) ^ 2 := by
  rw [pow_mul]
  congr 1
  ring

lemma chain_step {P R S Q : (ZMod 1249)[X]}
    (h : F10 ∣ P - R) (hstep : R ^ 2 = F10 * Q + S) :
    F10 ∣ P ^ 2 - S := by
  obtain ⟨A, hA⟩ := h
  refine ⟨Q + 2 * R * A + F10 * A ^ 2, ?_⟩
  have hP : P = R + F10 * A := by
    linear_combination hA
  rw [hP]
  rw [show (R + F10 * A) ^ 2 = R ^ 2 + F10 * (2 * R * A + F10 * A ^ 2) by ring]
  rw [hstep]
  ring

lemma stepEq0 : S2560Batch1Actual.R0 ^ 2 = F10 * Q0 + S2560Batch1Actual.R1 := by
  rw [show S2560Batch1Actual.R0 ^ 2 = (X ^ 2 * 1) by unfold S2560Batch1Actual.R0; ring]
  rw [step0]
  rfl

lemma stepEq1 : S2560Batch1Actual.R1 ^ 2 = F10 * Q1 + S2560Batch1Actual.R2 := by
  rw [show S2560Batch1Actual.R1 ^ 2 = (X ^ 4 * 1) by unfold S2560Batch1Actual.R1; ring]
  rw [step1]
  rfl

lemma stepEq2 : S2560Batch1Actual.R2 ^ 2 = F10 * Q2 + S2560Batch1Actual.R3 := by
  rw [show S2560Batch1Actual.R2 ^ 2 = (X ^ 8 * 1) by unfold S2560Batch1Actual.R2; ring]
  rw [step2]
  rfl

lemma stepEq3 : S2560Batch1Actual.R3 ^ 2 = F10 * Q3 + S2560Batch1Actual.R4 := by
  rw [show S2560Batch1Actual.R3 ^ 2 = (X ^ 16 * 1) by unfold S2560Batch1Actual.R3; ring]
  rw [step3]
  rfl

lemma stepEq4 : S2560Batch1Actual.R4 ^ 2 = F10 * Q4 + S2560Batch1Actual.R5 := by
  rw [show S2560Batch1Actual.R4 ^ 2 = (573 + X * 1201 + X ^ 2 * 881 + X ^ 3 * 886 + X ^ 4 * 862 + X ^ 5 * 5 + X ^ 6 * 1181 + X ^ 7 * 658 + X ^ 8 * 1105 + X ^ 9 * 773 + X ^ 10 * 380 + X ^ 11 * 649 + X ^ 12 * 559 + X ^ 13 * 212 + X ^ 14 * 710 + X ^ 15 * 161 + X ^ 16 * 518 + X ^ 17 * 138 + X ^ 18 * 1159) by unfold S2560Batch1Actual.R4; ring]
  rw [step4]
  rfl

lemma stepEq5 : S2560Batch1Actual.R5 ^ 2 = F10 * Q5 + S2560Batch1Actual.R6 := by
  rw [show S2560Batch1Actual.R5 ^ 2 = (749 + X * 464 + X ^ 2 * 505 + X ^ 3 * 1049 + X ^ 4 * 663 + X ^ 5 * 46 + X ^ 6 * 169 + X ^ 7 * 448 + X ^ 8 * 1109 + X ^ 9 * 819 + X ^ 10 * 81 + X ^ 11 * 897 + X ^ 12 * 729 + X ^ 13 * 627 + X ^ 14 * 387 + X ^ 15 * 277 + X ^ 16 * 302 + X ^ 17 * 1177 + X ^ 18 * 483) by unfold S2560Batch1Actual.R5; ring]
  rw [step5]
  rfl

lemma stepEq6 : S2560Batch1Actual.R6 ^ 2 = F10 * Q6 + S2560Batch1Actual.R7 := by
  rw [show S2560Batch1Actual.R6 ^ 2 = (569 + X * 1117 + X ^ 2 * 765 + X ^ 3 * 299 + X ^ 4 * 607 + X ^ 5 * 380 + X ^ 6 * 746 + X ^ 7 * 413 + X ^ 8 * 37 + X ^ 9 * 987 + X ^ 10 * 122 + X ^ 11 * 913 + X ^ 12 * 555 + X ^ 13 * 514 + X ^ 14 * 361 + X ^ 15 * 828 + X ^ 16 * 139 + X ^ 17 * 331 + X ^ 18 * 857) by unfold S2560Batch1Actual.R6; ring]
  rw [step6]
  rfl

lemma stepEq7 : S2560Batch1Actual.R7 ^ 2 = F10 * Q7 + S2560Batch1Actual.R8 := by
  rw [show S2560Batch1Actual.R7 ^ 2 = (1185 + X * 174 + X ^ 2 * 834 + X ^ 3 * 552 + X ^ 4 * 551 + X ^ 5 * 812 + X ^ 6 * 559 + X ^ 7 * 549 + X ^ 8 * 374 + X ^ 9 * 964 + X ^ 10 * 250 + X ^ 11 * 331 + X ^ 12 * 862 + X ^ 13 * 1234 + X ^ 14 * 466 + X ^ 15 * 253 + X ^ 16 * 332 + X ^ 17 * 393 + X ^ 18 * 51) by unfold S2560Batch1Actual.R7; ring]
  rw [step7]
  rfl

lemma stepEq8 : S2560Batch1Actual.R8 ^ 2 = F10 * Q8 + S2560Batch1Actual.R9 := by
  rw [show S2560Batch1Actual.R8 ^ 2 = (170 + X * 1239 + X ^ 3 * 1082 + X ^ 4 * 715 + X ^ 5 * 47 + X ^ 6 * 417 + X ^ 7 * 780 + X ^ 8 * 755 + X ^ 9 * 203 + X ^ 10 * 1105 + X ^ 11 * 978 + X ^ 12 * 972 + X ^ 13 * 156 + X ^ 14 * 799 + X ^ 15 * 167 + X ^ 16 * 787 + X ^ 17 * 1108 + X ^ 18 * 877) by unfold S2560Batch1Actual.R8; ring]
  rw [step8]
  rfl

lemma stepEq9 : S2560Batch1Actual.R9 ^ 2 = F10 * Q9 + S2560Batch1Actual.R10 := by
  rw [show S2560Batch1Actual.R9 ^ 2 = (161 + X * 383 + X ^ 2 * 451 + X ^ 3 * 390 + X ^ 4 * 551 + X ^ 5 * 54 + X ^ 6 * 90 + X ^ 7 * 273 + X ^ 8 * 999 + X ^ 9 * 138 + X ^ 10 * 36 + X ^ 11 * 164 + X ^ 12 * 1030 + X ^ 13 * 371 + X ^ 14 * 571 + X ^ 15 * 1230 + X ^ 16 * 980 + X ^ 17 * 761 + X ^ 18 * 664) by unfold S2560Batch1Actual.R9; ring]
  rw [step9]
  rfl

theorem chain0 : F10 ∣ X ^ (2 ^ 0) - S2560Batch1Actual.R0 := by
  have h : S2560Batch1Actual.R0 = X := by unfold S2560Batch1Actual.R0; ring
  rw [h, sub_self]
  exact dvd_zero _

theorem chain1 : F10 ∣ X ^ (2 ^ 1) - S2560Batch1Actual.R1 := by
  rw [show 1 = 0 + 1 by norm_num, pow_two_succ]
  exact chain_step chain0 stepEq0

theorem chain2 : F10 ∣ X ^ (2 ^ 2) - S2560Batch1Actual.R2 := by
  rw [show 2 = 1 + 1 by norm_num, pow_two_succ]
  exact chain_step chain1 stepEq1

theorem chain3 : F10 ∣ X ^ (2 ^ 3) - S2560Batch1Actual.R3 := by
  rw [show 3 = 2 + 1 by norm_num, pow_two_succ]
  exact chain_step chain2 stepEq2

theorem chain4 : F10 ∣ X ^ (2 ^ 4) - S2560Batch1Actual.R4 := by
  rw [show 4 = 3 + 1 by norm_num, pow_two_succ]
  exact chain_step chain3 stepEq3

theorem chain5 : F10 ∣ X ^ (2 ^ 5) - S2560Batch1Actual.R5 := by
  rw [show 5 = 4 + 1 by norm_num, pow_two_succ]
  exact chain_step chain4 stepEq4

theorem chain6 : F10 ∣ X ^ (2 ^ 6) - S2560Batch1Actual.R6 := by
  rw [show 6 = 5 + 1 by norm_num, pow_two_succ]
  exact chain_step chain5 stepEq5

theorem chain7 : F10 ∣ X ^ (2 ^ 7) - S2560Batch1Actual.R7 := by
  rw [show 7 = 6 + 1 by norm_num, pow_two_succ]
  exact chain_step chain6 stepEq6

theorem chain8 : F10 ∣ X ^ (2 ^ 8) - S2560Batch1Actual.R8 := by
  rw [show 8 = 7 + 1 by norm_num, pow_two_succ]
  exact chain_step chain7 stepEq7

theorem chain9 : F10 ∣ X ^ (2 ^ 9) - S2560Batch1Actual.R9 := by
  rw [show 9 = 8 + 1 by norm_num, pow_two_succ]
  exact chain_step chain8 stepEq8

theorem chain10 : F10 ∣ X ^ (2 ^ 10) - S2560Batch1Actual.R10 := by
  rw [show 10 = 9 + 1 by norm_num, pow_two_succ]
  exact chain_step chain9 stepEq9

end LeanFormal.IUT.XiFPaper.S2575PowerTwoCongruenceActual

end