import tmp.sheaf.xif.paper.S2590Q1249ChainActual
import tmp.sheaf.xif.paper.S2561Batch2CorrectActual
import tmp.sheaf.xif.paper.S2562Batch3CorrectActual
import tmp.sheaf.xif.paper.S2570Bezout2Actual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2589ProductDActual
open LeanFormal.IUT.XiFPaper.S2590Q1249ChainActual
open LeanFormal.IUT.XiFPaper.S2561Batch2CorrectActual
open LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual
open LeanFormal.IUT.XiFPaper.S2570Bezout2Actual

namespace LeanFormal.IUT.XiFPaper.S2593HBez2ChainActualAdapted

abbrev F10 : (ZMod 1249)[X] := S2550F10

lemma dvd_mul_shift {a a' b b' : (ZMod 1249)[X]}
    (ha : F10 ∣ a - a') (hb : F10 ∣ b - b') :
    F10 ∣ a * b - a' * b' := by
  have h : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [h]
  exact dvd_add (dvd_mul_of_dvd_left ha b) (dvd_mul_of_dvd_right hb a')

lemma dvd_sq_step {a : Nat} {U V Q : (ZMod 1249)[X]}
    (h : F10 ∣ (X : (ZMod 1249)[X]) ^ a - U)
    (hstep : U * U = F10 * Q + V) :
    F10 ∣ (X : (ZMod 1249)[X]) ^ (2 * a) - V := by
  have h1 : F10 ∣ (X : (ZMod 1249)[X]) ^ a * X ^ a - U * U :=
    dvd_mul_shift h h
  have h2 : F10 ∣ U * U - V := by
    rw [hstep]
    simpa [add_sub_cancel_right] using dvd_mul_right F10 Q
  have hsum := dvd_add h1 h2
  convert hsum using 1
  rw [show 2 * a = a + a by omega, pow_add]
  ring

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
  convert hsum using 1
  rw [pow_add]
  ring

theorem chain1249sq : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249) - V4 := by
  have h0 : F10 ∣ (X : (ZMod 1249)[X]) ^ 1249 - U0 := by
    change F10 ∣ (X : (ZMod 1249)[X]) ^ 1249 - rD
    exact chain1249
  have h1 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 2) - U1 := by
    have h := dvd_sq_step (a := 1249) (U := U0) (V := U1) (Q := Qustep0) h0 (by
      change Austep0 * Bustep0 = S2550F10 * Qustep0 + Nustep0
      exact ustep0)
    convert h using 1 <;> ring
  have h2 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 4) - U2 := by
    have h := dvd_sq_step (a := 1249 * 2) (U := U1) (V := U2) (Q := Qustep1) h1 (by
      change Austep1 * Bustep1 = S2550F10 * Qustep1 + Nustep1
      exact ustep1)
    convert h using 1 <;> ring
  have h3 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 8) - U3 := by
    have h := dvd_sq_step (a := 1249 * 4) (U := U2) (V := U3) (Q := Qustep2) h2 (by
      change Austep2 * Bustep2 = S2550F10 * Qustep2 + Nustep2
      exact ustep2)
    convert h using 1 <;> ring
  have h4 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 16) - U4 := by
    have h := dvd_sq_step (a := 1249 * 8) (U := U3) (V := U4) (Q := Qustep3) h3 (by
      change Austep3 * Bustep3 = S2550F10 * Qustep3 + Nustep3
      exact ustep3)
    convert h using 1 <;> ring
  have h5 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 32) - U5 := by
    have h := dvd_sq_step (a := 1249 * 16) (U := U4) (V := U5) (Q := Qustep4) h4 (by
      change Austep4 * Bustep4 = S2550F10 * Qustep4 + Nustep4
      exact ustep4)
    convert h using 1 <;> ring
  have h6 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 64) - U6 := by
    have h := dvd_sq_step (a := 1249 * 32) (U := U5) (V := U6) (Q := Qustep5) h5 (by
      change Austep5 * Bustep5 = S2550F10 * Qustep5 + Nustep5
      exact ustep5)
    convert h using 1 <;> ring
  have h7 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 128) - U7 := by
    have h := dvd_sq_step (a := 1249 * 64) (U := U6) (V := U7) (Q := Qustep6) h6 (by
      change Austep6 * Bustep6 = S2550F10 * Qustep6 + Nustep6
      exact ustep6)
    convert h using 1 <;> ring
  have h8 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 256) - U8 := by
    have h := dvd_sq_step (a := 1249 * 128) (U := U7) (V := U8) (Q := Qustep7) h7 (by
      change Austep7 * Bustep7 = S2550F10 * Qustep7 + Nustep7
      exact ustep7)
    convert h using 1 <;> ring
  have h9 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 512) - U9 := by
    have h := dvd_sq_step (a := 1249 * 256) (U := U8) (V := U9) (Q := Qustep8) h8 (by
      change Austep8 * Bustep8 = S2550F10 * Qustep8 + Nustep8
      exact ustep8)
    convert h using 1 <;> ring
  have h10 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1024) - U10 := by
    have h := dvd_sq_step (a := 1249 * 512) (U := U9) (V := U10) (Q := Qustep9) h9 (by
      change Austep9 * Bustep9 = S2550F10 * Qustep9 + Nustep9
      exact ustep9)
    convert h using 1 <;> ring
  have hV0 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1024) - V0 := by
    change F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1024) - U10
    exact h10
  have hV1 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1152) - V1 := by
    have h := dvd_mul_step (a := 1249 * 1024) (b := 1249 * 128)
      (U := V0) (B := U7) (V := V1) hV0 h7 (by
        rw [show V0 = Avstep0 from rfl,
          show U7 = Bvstep0 from rfl,
          show V1 = Nvstep0 from rfl]
        exact vstep0)
    convert h using 1 <;> ring
  have hV2 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1216) - V2 := by
    have h := dvd_mul_step (a := 1249 * 1152) (b := 1249 * 64)
      (U := V1) (B := U6) (V := V2) hV1 h6 (by
        rw [show V1 = Avstep1 from rfl,
          show U6 = Bvstep1 from rfl,
          show V2 = Nvstep1 from rfl]
        exact vstep1)
    convert h using 1 <;> ring
  have hV3 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1248) - V3 := by
    have h := dvd_mul_step (a := 1249 * 1216) (b := 1249 * 32)
      (U := V2) (B := U5) (V := V3) hV2 h5 (by
        rw [show V2 = Avstep2 from rfl,
          show U5 = Bvstep2 from rfl,
          show V3 = Nvstep2 from rfl]
        exact vstep2)
    convert h using 1 <;> ring
  have hV4 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249) - V4 := by
    have h := dvd_mul_step (a := 1249 * 1248) (b := 1249)
      (U := V3) (B := U0) (V := V4) hV3 h0 (by
        rw [show V3 = Avstep3 from rfl,
          show U0 = Bvstep3 from rfl,
          show V4 = Nvstep3 from rfl]
        exact vstep3)
    convert h using 1 <;> ring
  exact hV4

theorem hbez2 : ∃ A B : (ZMod 1249)[X],
    A * F10 + B * ((X : (ZMod 1249)[X]) ^ (1249 * 1249) - X) = 1 := by
  obtain ⟨q, hq⟩ := chain1249sq
  refine ⟨A2 - B2 * q, B2, ?_⟩
  have hS : S2 = V4 - X := by
    ext n
    by_cases hn : n ≤ 9
    · interval_cases n <;>
        (simp [S2, V4, Polynomial.coeff_sub, Polynomial.coeff_X] <;> decide)
    · have h1 : S2.coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : S2.natDegree ≤ 9 := by unfold S2; compute_degree!
        omega
      have h2 : V4.coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        have h : V4.natDegree ≤ 9 := by unfold V4; compute_degree!
        omega
      rw [h1, h2, coeff_sub, coeff_X, if_neg (by omega)]
      simp
  calc
    (A2 - B2 * q) * F10 + B2 * ((X : (ZMod 1249)[X]) ^ (1249 * 1249) - X)
        = A2 * F10 + B2 * S2 := by
          rw [hS]
          rw [hq]
          ring
    _ = 1 := bezout2

end LeanFormal.IUT.XiFPaper.S2593HBez2ChainActualAdapted
end
