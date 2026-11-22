import tmp.sheaf.xif.paper.S2593aUChainActual
import tmp.sheaf.xif.paper.S2562Batch3CorrectActual
import tmp.sheaf.xif.paper.S2570Bezout2Actual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual
open LeanFormal.IUT.XiFPaper.S2561Batch2CorrectActual
open LeanFormal.IUT.XiFPaper.S2570Bezout2Actual
open LeanFormal.IUT.XiFPaper.S2593aUChainActual

namespace LeanFormal.IUT.XiFPaper.S2593bVChainActual

abbrev F10 : (ZMod 1249)[X] := S2550F10

lemma dvd_mul_shift {a a' b b' : (ZMod 1249)[X]}
    (ha : F10 ∣ a - a') (hb : F10 ∣ b - b') :
    F10 ∣ a * b - a' * b' := by
  have h : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [h]
  exact dvd_add (dvd_mul_of_dvd_left ha b) (dvd_mul_of_dvd_right hb a')

lemma dvd_mul_step {a b : Nat} {U B V Q : (ZMod 1249)[X]}
    (hU : F10 ∣ (X : (ZMod 1249)[X]) ^ a - U)
    (hB : F10 ∣ (X : (ZMod 1249)[X]) ^ b - B)
    (hstep : U * B = F10 * Q + V) :
    F10 ∣ (X : (ZMod 1249)[X]) ^ (a + b) - V := by
  have h1 : F10 ∣ (X : (ZMod 1249)[X]) ^ a * X ^ b - U * B :=
    dvd_mul_shift hU hB
  have h2 : F10 ∣ U * B - V := by
    rw [hstep]
    simpa [add_sub_cancel_right] using dvd_mul_right F10 Q
  have hsum := dvd_add h1 h2
  rw [pow_add]
  convert hsum using 1
  ring

lemma V0_eq_U10 : V0 = U10 := by
  ext n
  by_cases hn : n ≤ 9
  · interval_cases n <;> (simp [V0, U10] <;> decide)
  · have h1 : V0.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : V0.natDegree ≤ 9 := by unfold V0; compute_degree!
      omega
    have h2 : U10.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : U10.natDegree ≤ 9 := by unfold U10; compute_degree!
      omega
    rw [h1, h2]


lemma hstepV0 : V0 * U7 = F10 * Qvstep0 + V1 := by
  have hV : V0.natDegree ≤ 9 := by unfold V0; compute_degree!
  have hU : U7.natDegree ≤ 9 := by unfold U7; compute_degree!
  have hQ : Qvstep0.natDegree ≤ 8 := by unfold Qvstep0; compute_degree!
  have hF : F10.natDegree = 10 := by unfold F10 S2550F10; compute_degree!
  have hN : V1.natDegree ≤ 9 := by unfold V1; compute_degree!
  have hL : (V0 * U7).natDegree ≤ 18 := by
    calc (V0 * U7).natDegree ≤ V0.natDegree + U7.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * Qvstep0).natDegree ≤ 18 := by
    calc (F10 * Qvstep0).natDegree ≤ F10.natDegree + Qvstep0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (F10 * Qvstep0 + V1).natDegree ≤ 18 := by
    calc (F10 * Qvstep0 + V1).natDegree ≤ max (F10 * Qvstep0).natDegree V1.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [V0, U7, Qvstep0, V1, F10, S2550F10, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma hstepV1 : V1 * U6 = F10 * Qvstep1 + V2 := by
  have hV : V1.natDegree ≤ 9 := by unfold V1; compute_degree!
  have hU : U6.natDegree ≤ 9 := by unfold U6; compute_degree!
  have hQ : Qvstep1.natDegree ≤ 8 := by unfold Qvstep1; compute_degree!
  have hF : F10.natDegree = 10 := by unfold F10 S2550F10; compute_degree!
  have hN : V2.natDegree ≤ 9 := by unfold V2; compute_degree!
  have hL : (V1 * U6).natDegree ≤ 18 := by
    calc (V1 * U6).natDegree ≤ V1.natDegree + U6.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * Qvstep1).natDegree ≤ 18 := by
    calc (F10 * Qvstep1).natDegree ≤ F10.natDegree + Qvstep1.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (F10 * Qvstep1 + V2).natDegree ≤ 18 := by
    calc (F10 * Qvstep1 + V2).natDegree ≤ max (F10 * Qvstep1).natDegree V2.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [V1, U6, Qvstep1, V2, F10, S2550F10, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma hstepV2 : V2 * U5 = F10 * Qvstep2 + V3 := by
  have hV : V2.natDegree ≤ 9 := by unfold V2; compute_degree!
  have hU : U5.natDegree ≤ 9 := by unfold U5; compute_degree!
  have hQ : Qvstep2.natDegree ≤ 8 := by unfold Qvstep2; compute_degree!
  have hF : F10.natDegree = 10 := by unfold F10 S2550F10; compute_degree!
  have hN : V3.natDegree ≤ 9 := by unfold V3; compute_degree!
  have hL : (V2 * U5).natDegree ≤ 18 := by
    calc (V2 * U5).natDegree ≤ V2.natDegree + U5.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * Qvstep2).natDegree ≤ 18 := by
    calc (F10 * Qvstep2).natDegree ≤ F10.natDegree + Qvstep2.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (F10 * Qvstep2 + V3).natDegree ≤ 18 := by
    calc (F10 * Qvstep2 + V3).natDegree ≤ max (F10 * Qvstep2).natDegree V3.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [V2, U5, Qvstep2, V3, F10, S2550F10, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma hstepV3 : V3 * U0 = F10 * Qvstep3 + V4 := by
  have hV : V3.natDegree ≤ 9 := by unfold V3; compute_degree!
  have hU : U0.natDegree ≤ 9 := by unfold U0; compute_degree!
  have hQ : Qvstep3.natDegree ≤ 8 := by unfold Qvstep3; compute_degree!
  have hF : F10.natDegree = 10 := by unfold F10 S2550F10; compute_degree!
  have hN : V4.natDegree ≤ 9 := by unfold V4; compute_degree!
  have hL : (V3 * U0).natDegree ≤ 18 := by
    calc (V3 * U0).natDegree ≤ V3.natDegree + U0.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have h1 : (F10 * Qvstep3).natDegree ≤ 18 := by
    calc (F10 * Qvstep3).natDegree ≤ F10.natDegree + Qvstep3.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 18 := by omega
  have hR : (F10 * Qvstep3 + V4).natDegree ≤ 18 := by
    calc (F10 * Qvstep3 + V4).natDegree ≤ max (F10 * Qvstep3).natDegree V4.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 18 := max_le h1 (by omega)
  apply Polynomial.ext; intro n
  by_cases hn : n ≤ 18
  · interval_cases n <;>
      (simp [V3, U0, Qvstep3, V4, F10, S2550F10, S2550F10, Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] <;> decide)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

theorem chain1249sq : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249) - V4 := by
  have hV0 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1024) - V0 := by
    rw [V0_eq_U10]
    exact hU10
  have hV1 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1152) - V1 := by
    have h := dvd_mul_step (a := 1249 * 1024) (b := 1249 * 128)
      (U := V0) (B := U7) (V := V1) hV0 hU7 hstepV0
    simpa [show 1249 * 1024 + 1249 * 128 = 1249 * 1152 by ring] using h
  have hV2 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1216) - V2 := by
    have h := dvd_mul_step (a := 1249 * 1152) (b := 1249 * 64)
      (U := V1) (B := U6) (V := V2) hV1 hU6 hstepV1
    simpa [show 1249 * 1152 + 1249 * 64 = 1249 * 1216 by ring] using h
  have hV3 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1248) - V3 := by
    have h := dvd_mul_step (a := 1249 * 1216) (b := 1249 * 32)
      (U := V2) (B := U5) (V := V3) hV2 hU5 hstepV2
    simpa [show 1249 * 1216 + 1249 * 32 = 1249 * 1248 by ring] using h
  have hV4 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249) - V4 := by
    have h := dvd_mul_step (a := 1249 * 1248) (b := 1249)
      (U := V3) (B := U0) (V := V4) hV3 hU0 hstepV3
    simpa [show 1249 * 1248 + 1249 = 1249 * 1249 by ring] using h
  exact hV4

theorem hbez2 : ∃ A B : (ZMod 1249)[X],
    A * F10 + B * ((X : (ZMod 1249)[X]) ^ (1249 * 1249) - X) = 1 := by
  obtain ⟨q, hq⟩ := chain1249sq
  refine ⟨S2570Bezout2Actual.A2 - S2570Bezout2Actual.B2 * q, S2570Bezout2Actual.B2, ?_⟩
  have hS : S2570Bezout2Actual.S2 = V4 - X := by
    ext n
    by_cases hn : n ≤ 9
    · interval_cases n <;>
        (simp [S2570Bezout2Actual.S2, V4, Polynomial.coeff_sub, Polynomial.coeff_X] <;> decide)
    · have h1 : S2570Bezout2Actual.S2.coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : S2570Bezout2Actual.S2.natDegree ≤ 9 := by unfold S2570Bezout2Actual.S2; compute_degree!
        omega
      have h2 : V4.coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : V4.natDegree ≤ 9 := by unfold V4; compute_degree!
        omega
      have hn0 : n ≠ 0 := by omega
      simp [Polynomial.coeff_sub, h1, h2, Polynomial.coeff_X, hn0]
      omega
  have hX : (X : (ZMod 1249)[X]) ^ (1249 * 1249) - X = F10 * q + (V4 - X) := by
    rw [show (X : (ZMod 1249)[X]) ^ (1249 * 1249) - X = ((X : (ZMod 1249)[X]) ^ (1249 * 1249) - V4) + (V4 - X) by ring, hq]
  calc
    (S2570Bezout2Actual.A2 - S2570Bezout2Actual.B2 * q) * F10 + S2570Bezout2Actual.B2 * ((X : (ZMod 1249)[X]) ^ (1249 * 1249) - X)
        = S2570Bezout2Actual.A2 * F10 + S2570Bezout2Actual.B2 * S2570Bezout2Actual.S2 := by
          rw [hS, hX]
          ring
    _ = 1 := bezout2



end LeanFormal.IUT.XiFPaper.S2593bVChainActual

end
