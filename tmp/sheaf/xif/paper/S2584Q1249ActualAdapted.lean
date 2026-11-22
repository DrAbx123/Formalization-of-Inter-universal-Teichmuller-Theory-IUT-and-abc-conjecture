import tmp.sheaf.xif.paper.S2560Batch1CorrectActual
import tmp.sheaf.xif.paper.S2582PowerTwoChainAltActual

/-! # S2584: X^1249 mod F10, stepwise product certificates -/

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual
open LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual

namespace LeanFormal.IUT.XiFPaper.S2584Q1249ActualAdapted

abbrev F : (ZMod 1249)[X] := S2550F10

def P1 : (ZMod 1249)[X] :=
  C 1220 + C 1205 * X + C 1059 * X^2 + C 718 * X^3 + C 467 * X^4 +
  C 434 * X^5 + C 1206 * X^6 + C 1159 * X^7 + C 1145 * X^8 +
  C 514 * X^9 + C 617 * X^10 + C 80 * X^11 + C 622 * X^12 +
  C 953 * X^13 + C 390 * X^14 + C 1188 * X^15 + C 633 * X^16 +
  C 637 * X^17 + C 1043 * X^18

def P2 : (ZMod 1249)[X] :=
  C 799 + C 1180 * X + C 905 * X^2 + C 872 * X^3 + C 1005 * X^4 +
  C 271 * X^5 + C 1018 * X^6 + C 1104 * X^7 + C 1035 * X^8 +
  C 343 * X^9 + C 1192 * X^10 + C 381 * X^11 + C 799 * X^12 +
  C 451 * X^13 + C 881 * X^14 + C 136 * X^15 + C 793 * X^16 +
  C 812 * X^17 + C 466 * X^18 + C 261 * X^19 + C 327 * X^20 +
  C 86 * X^21 + C 1194 * X^22 + C 464 * X^23 + C 533 * X^24 +
  C 959 * X^25 + C 681 * X^26 + C 789 * X^27

def P3 : (ZMod 1249)[X] :=
  C 118 + C 806 * X + C 319 * X^2 + C 1050 * X^3 + C 1217 * X^4 +
  C 132 * X^5 + C 1063 * X^6 + C 184 * X^7 + C 992 * X^8 +
  C 329 * X^9 + C 64 * X^10 + C 568 * X^11 + C 787 * X^12 +
  C 154 * X^13 + C 774 * X^14 + C 1226 * X^15 + C 1046 * X^16 +
  C 132 * X^17 + C 30 * X^18 + C 1202 * X^19 + C 194 * X^20 +
  C 607 * X^21 + C 599 * X^22 + C 747 * X^23 + C 651 * X^24 +
  C 1160 * X^25 + C 444 * X^26 + C 13 * X^27 + C 497 * X^28 +
  C 1150 * X^29 + C 385 * X^30 + C 35 * X^31 + C 99 * X^32 +
  C 1202 * X^33 + C 499 * X^34 + C 82 * X^35 + C 68 * X^36

def P4 : (ZMod 1249)[X] :=
  C 0 + C 118 * X + C 806 * X^2 + C 319 * X^3 + C 1050 * X^4 +
  C 1217 * X^5 + C 132 * X^6 + C 1063 * X^7 + C 184 * X^8 +
  C 992 * X^9 + C 329 * X^10 + C 64 * X^11 + C 568 * X^12 +
  C 787 * X^13 + C 154 * X^14 + C 774 * X^15 + C 1226 * X^16 +
  C 1046 * X^17 + C 132 * X^18 + C 30 * X^19 + C 1202 * X^20 +
  C 194 * X^21 + C 607 * X^22 + C 599 * X^23 + C 747 * X^24 +
  C 651 * X^25 + C 1160 * X^26 + C 444 * X^27 + C 13 * X^28 +
  C 497 * X^29 + C 1150 * X^30 + C 385 * X^31 + C 35 * X^32 +
  C 99 * X^33 + C 1202 * X^34 + C 499 * X^35 + C 82 * X^36 +
  C 68 * X^37

noncomputable def Q1249 : (ZMod 1249)[X] :=
  C 825 + C 559 * X + C 627 * X^2 + C 67 * X^3 + C 205 * X^4 +
  C 286 * X^5 + C 986 * X^6 + C 668 * X^7 + C 673 * X^8 +
  C 70 * X^9 + C 167 * X^10 + C 275 * X^11 + C 592 * X^12 +
  C 986 * X^13 + C 383 * X^14 + C 1013 * X^15 + C 369 * X^16 +
  C 110 * X^17 + C 187 * X^18 + C 26 * X^19 + C 67 * X^20 +
  C 645 * X^21 + C 329 * X^22 + C 680 * X^23 + C 1012 * X^24 +
  C 260 * X^25 + C 41 * X^26 + C 68 * X^27

noncomputable def R1249 : (ZMod 1249)[X] :=
  C 1116 + C 1078 * X + C 786 * X^2 + C 643 * X^3 + C 776 * X^4 +
  C 720 * X^5 + C 1083 * X^6 + C 988 * X^7 + C 1201 * X^8 + C 56 * X^9

theorem P1_cert : P1 = S2560Batch1CorrectActual.R10 * S2560Batch1CorrectActual.R7 := by
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [P1, S2560Batch1CorrectActual.R10, S2560Batch1CorrectActual.R7,
        Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · have hL : P1.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : P1.natDegree ≤ 18 := by unfold P1; compute_degree!
      omega
    have hR : (S2560Batch1CorrectActual.R10 * S2560Batch1CorrectActual.R7).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : (S2560Batch1CorrectActual.R10 * S2560Batch1CorrectActual.R7).natDegree ≤ 18 := by
        unfold S2560Batch1CorrectActual.R10 S2560Batch1CorrectActual.R7
        compute_degree!
      omega
    rw [hL, hR]

theorem P2_cert : P2 = P1 * S2560Batch1CorrectActual.R6 := by
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 27
  · interval_cases n <;>
      (simp [P2, P1, S2560Batch1CorrectActual.R6, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · have hL : P2.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : P2.natDegree ≤ 27 := by unfold P2; compute_degree!
      omega
    have hR : (P1 * S2560Batch1CorrectActual.R6).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : (P1 * S2560Batch1CorrectActual.R6).natDegree ≤ 27 := by
        unfold P1 S2560Batch1CorrectActual.R6; compute_degree!
      omega
    rw [hL, hR]

theorem P3_cert : P3 = P2 * S2560Batch1CorrectActual.R5 := by
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 36
  · interval_cases n <;>
      (simp [P3, P2, S2560Batch1CorrectActual.R5, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · have hL : P3.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : P3.natDegree ≤ 36 := by unfold P3; compute_degree!
      omega
    have hR : (P2 * S2560Batch1CorrectActual.R5).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : (P2 * S2560Batch1CorrectActual.R5).natDegree ≤ 36 := by
        unfold P2 S2560Batch1CorrectActual.R5; compute_degree!
      omega
    rw [hL, hR]

theorem P4_cert : P4 = P3 * S2560Batch1CorrectActual.R0 := by
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 37
  · interval_cases n <;>
      (simp [P4, P3, S2560Batch1CorrectActual.R0, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · have hL : P4.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : P4.natDegree ≤ 37 := by unfold P4; compute_degree!
      omega
    have hR : (P3 * S2560Batch1CorrectActual.R0).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : (P3 * S2560Batch1CorrectActual.R0).natDegree ≤ 37 := by
        unfold P3 S2560Batch1CorrectActual.R0; compute_degree!
      omega
    rw [hL, hR]

theorem product_cert : P4 = F * Q1249 + R1249 := by
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 37
  · interval_cases n <;>
      (simp [P4, Q1249, R1249, F, S2550F10, Polynomial.coeff_add,
        Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
  · have hL : P4.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : P4.natDegree ≤ 37 := by unfold P4; compute_degree!
      omega
    have hR : (F * Q1249 + R1249).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : (F * Q1249 + R1249).natDegree ≤ 37 := by
        unfold F Q1249 R1249; compute_degree!
      omega
    rw [hL, hR]

end LeanFormal.IUT.XiFPaper.S2584Q1249ActualAdapted
end
