import tmp.sheaf.xif.paper.S2594aWChainActual
import tmp.sheaf.xif.paper.S2563Batch4CorrectActual
import tmp.sheaf.xif.paper.S2572Bezout134Actual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2594bAChainActual
open LeanFormal.IUT.XiFPaper.S2594aWChainActual
abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10
private lemma dvd_mul_step {a b : Nat} {U B V Q : (ZMod 1249)[X]}
    (hU : F10 ∣ (X : (ZMod 1249)[X]) ^ a - U)
    (hB : F10 ∣ (X : (ZMod 1249)[X]) ^ b - B)
    (hstep : U * B = F10 * Q + V) :
    F10 ∣ (X : (ZMod 1249)[X]) ^ (a + b) - V := by
  have h1 : F10 ∣ (X : (ZMod 1249)[X]) ^ a * X ^ b - U * B := dvd_mul_shift hU hB
  have h2 : F10 ∣ U * B - V := by
    rw [hstep]
    simpa [add_sub_cancel_right] using dvd_mul_right F10 Q
  have hsum := dvd_add h1 h2
  have hpow : (X : (ZMod 1249)[X]) ^ (a + b) = X ^ a * X ^ b := by rw [pow_add]
  have hEq : (X : (ZMod 1249)[X]) ^ a * X ^ b - V =
      (X ^ a * X ^ b - U * B) + (U * B - V) := by ring
  rw [hpow, hEq]
  exact hsum
lemma A0_eq_W10 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A0 = LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W10 := by
  ext n
  by_cases hn : n ≤ 9
  · interval_cases n <;>
      (simp [LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A0, LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W10] <;> decide)
  · have h1 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A0.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A0.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A0; compute_degree!
      omega
    have h2 : LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W10.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W10.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W10; compute_degree!
      omega
    rw [h1, h2]
lemma hA0 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1024) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A0 := by
  rw [A0_eq_W10]
  exact hW10
lemma hA1 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1152) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A1 := by
  have hstep : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A0 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W7 = F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep0 + LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A1 := by
    ext n
    by_cases hn : n ≤ 18
    · interval_cases n <;>
        (simp [LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A0, LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W7, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep0, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A1, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10,
          Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X,
          Polynomial.coeff_X_pow, Polynomial.coeff_one,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
    · have h1 : (LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A0 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W7).coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : (LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A0 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W7).natDegree ≤ 18 := by
          calc _ ≤ LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A0.natDegree + LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W7.natDegree := Polynomial.natDegree_mul_le
            _ ≤ 18 := by
              have hA : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A0.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A0; compute_degree!
              have hW : LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W7.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W7; compute_degree!
              omega
        omega
      have h2 : (F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep0).coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : (F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep0).natDegree ≤ 18 := by
          calc _ ≤ F10.natDegree + LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep0.natDegree := Polynomial.natDegree_mul_le
            _ ≤ 18 := by
              have hF : F10.natDegree = 10 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
              have hQ : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep0.natDegree ≤ 8 := by unfold LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep0; compute_degree!
              omega
        omega
      have h3 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A1.coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A1.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A1; compute_degree!
        omega
      rw [h1, Polynomial.coeff_add, h2, h3]
      norm_num

  have h := dvd_mul_step (a := (1249 * 1249) * 1024) (b := (1249 * 1249) * 128) (U := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A0) (B := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W7) (V := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A1) hA0 hW7 hstep
  simpa [show (1249 * 1249) * 1024 + (1249 * 1249) * 128 = (1249 * 1249) * 1152 by ring] using h
lemma hA2 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1216) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A2 := by
  have hstep : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A1 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W6 = F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep1 + LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A2 := by
    ext n
    by_cases hn : n ≤ 18
    · interval_cases n <;>
        (simp [LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A1, LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W6, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep1, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A2, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10,
          Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X,
          Polynomial.coeff_X_pow, Polynomial.coeff_one,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
    · have h1 : (LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A1 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W6).coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : (LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A1 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W6).natDegree ≤ 18 := by
          calc _ ≤ LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A1.natDegree + LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W6.natDegree := Polynomial.natDegree_mul_le
            _ ≤ 18 := by
              have hA : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A1.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A1; compute_degree!
              have hW : LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W6.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W6; compute_degree!
              omega
        omega
      have h2 : (F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep1).coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : (F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep1).natDegree ≤ 18 := by
          calc _ ≤ F10.natDegree + LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep1.natDegree := Polynomial.natDegree_mul_le
            _ ≤ 18 := by
              have hF : F10.natDegree = 10 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
              have hQ : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep1.natDegree ≤ 8 := by unfold LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep1; compute_degree!
              omega
        omega
      have h3 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A2.coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A2.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A2; compute_degree!
        omega
      rw [h1, Polynomial.coeff_add, h2, h3]
      norm_num

  have h := dvd_mul_step (a := (1249 * 1249) * 1152) (b := (1249 * 1249) * 64) (U := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A1) (B := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W6) (V := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A2) hA1 hW6 hstep
  simpa [show (1249 * 1249) * 1152 + (1249 * 1249) * 64 = (1249 * 1249) * 1216 by ring] using h
lemma hA3 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1248) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A3 := by
  have hstep : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A2 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W5 = F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep2 + LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A3 := by
    ext n
    by_cases hn : n ≤ 18
    · interval_cases n <;>
        (simp [LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A2, LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W5, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep2, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A3, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10,
          Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X,
          Polynomial.coeff_X_pow, Polynomial.coeff_one,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
    · have h1 : (LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A2 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W5).coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : (LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A2 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W5).natDegree ≤ 18 := by
          calc _ ≤ LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A2.natDegree + LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W5.natDegree := Polynomial.natDegree_mul_le
            _ ≤ 18 := by
              have hA : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A2.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A2; compute_degree!
              have hW : LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W5.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W5; compute_degree!
              omega
        omega
      have h2 : (F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep2).coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : (F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep2).natDegree ≤ 18 := by
          calc _ ≤ F10.natDegree + LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep2.natDegree := Polynomial.natDegree_mul_le
            _ ≤ 18 := by
              have hF : F10.natDegree = 10 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
              have hQ : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep2.natDegree ≤ 8 := by unfold LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep2; compute_degree!
              omega
        omega
      have h3 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A3.coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A3.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A3; compute_degree!
        omega
      rw [h1, Polynomial.coeff_add, h2, h3]
      norm_num

  have h := dvd_mul_step (a := (1249 * 1249) * 1216) (b := (1249 * 1249) * 32) (U := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A2) (B := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W5) (V := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A3) hA2 hW5 hstep
  simpa [show (1249 * 1249) * 1216 + (1249 * 1249) * 32 = (1249 * 1249) * 1248 by ring] using h
lemma hA4 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1249) - LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4 := by
  have hstep : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A3 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W0 = F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep3 + LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4 := by
    ext n
    by_cases hn : n ≤ 18
    · interval_cases n <;>
        (simp [LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A3, LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W0, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep3, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4, F10, LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10,
          Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_C, Polynomial.coeff_X,
          Polynomial.coeff_X_pow, Polynomial.coeff_one,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] <;> decide)
    · have h1 : (LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A3 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W0).coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : (LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A3 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W0).natDegree ≤ 18 := by
          calc _ ≤ LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A3.natDegree + LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W0.natDegree := Polynomial.natDegree_mul_le
            _ ≤ 18 := by
              have hA : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A3.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A3; compute_degree!
              have hW : LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W0.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W0; compute_degree!
              omega
        omega
      have h2 : (F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep3).coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : (F10 * LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep3).natDegree ≤ 18 := by
          calc _ ≤ F10.natDegree + LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep3.natDegree := Polynomial.natDegree_mul_le
            _ ≤ 18 := by
              have hF : F10.natDegree = 10 := by unfold F10 LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10; compute_degree!
              have hQ : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep3.natDegree ≤ 8 := by unfold LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.Qastep3; compute_degree!
              omega
        omega
      have h3 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4.coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4; compute_degree!
        omega
      rw [h1, Polynomial.coeff_add, h2, h3]
      norm_num

  have h := dvd_mul_step (a := (1249 * 1249) * 1248) (b := 1249 * 1249) (U := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A3) (B := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W0) (V := LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4) hA3 hW0 hstep
  simpa [show (1249 * 1249) * 1248 + (1249 * 1249) = (1249 * 1249) * 1249 by ring] using h
theorem hbez3 : ∃ A B : (ZMod 1249)[X],
    A * F10 + B * ((X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249) - X) = 1 := by
  obtain ⟨q, hq⟩ := hA4
  refine ⟨LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.A3 - LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.B3 * q, LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.B3, ?_⟩
  have hS : LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.S3 = LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4 - X := by
    ext n
    by_cases hn : n ≤ 9
    · interval_cases n <;>
        (simp [LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.S3, LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4, Polynomial.coeff_sub, Polynomial.coeff_X] <;> decide)
    · have h1 : LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.S3.coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.S3.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.S3; compute_degree!
        omega
      have h2 : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4.coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4; compute_degree!
        omega
      have hx : (X : (ZMod 1249)[X]).coeff n = 0 := by rw [coeff_X, if_neg (by omega)]
      rw [h1, coeff_sub, h2, hx, sub_zero]
  have hq' : (X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249) - X = F10 * q + (LeanFormal.IUT.XiFPaper.S2563Batch4CorrectActual.A4 - X) := by
    rw [← hq]; ring
  calc
    (LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.A3 - LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.B3 * q) * F10 + LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.B3 * ((X : (ZMod 1249)[X]) ^ (1249 * 1249 * 1249) - X)
        = LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.A3 * F10 + LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.B3 * LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.S3 := by rw [hS, hq']; ring
    _ = 1 := LeanFormal.IUT.XiFPaper.S2572Bezout134Actual.bezout3
#check hbez3
end LeanFormal.IUT.XiFPaper.S2594bAChainActual
end
