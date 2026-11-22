import tmp.sheaf.xif.paper.S2590Q1249ChainActual
import tmp.sheaf.xif.paper.S2561Batch2CorrectActual

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2561Batch2CorrectActual

namespace LeanFormal.IUT.XiFPaper.S2593aUChainActual

local notation "X" => Polynomial.X

lemma dvd_mul_shift {a a' b b' : (ZMod 1249)[X]}
    (ha : S2550F10 ∣ a - a') (hb : S2550F10 ∣ b - b') :
    S2550F10 ∣ a * b - a' * b' := by
  have h : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [h]
  exact dvd_add (dvd_mul_of_dvd_left ha b) (dvd_mul_of_dvd_right hb a')

lemma dvd_sq_step {a : Nat} {U V Q : (ZMod 1249)[X]}
    (h : S2550F10 ∣ (X : (ZMod 1249)[X]) ^ a - U)
    (hstep : U * U = S2550F10 * Q + V) :
    S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (2 * a) - V := by
  have h1 : S2550F10 ∣ (X : (ZMod 1249)[X]) ^ a * X ^ a - U * U :=
    dvd_mul_shift h h
  have h2 : S2550F10 ∣ U * U - V := by
    rw [hstep]
    simpa [add_sub_cancel_right] using dvd_mul_right S2550F10 Q
  have hsum := dvd_add h1 h2
  have hpow : (X : (ZMod 1249)[X]) ^ (2 * a) = X ^ a * X ^ a := by
    rw [show 2 * a = a + a by omega, pow_add]
  rw [hpow]
  convert hsum using 1
  ring

lemma hU0 : S2550F10 ∣ (X : (ZMod 1249)[X]) ^ 1249 - U0 := by
  have hU0eq : U0 = LeanFormal.IUT.XiFPaper.S2589ProductDActual.rD := rfl
  simpa [hU0eq] using LeanFormal.IUT.XiFPaper.S2590Q1249ChainActual.chain1249
lemma hU1 : S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 2) - U1 := by
  have h := dvd_sq_step (a := 1249 * 1) (U := U0) (V := U1) (Q := Qustep0) hU0 (by
    simpa [Austep0, Bustep0, Nustep0, U0, U1] using ustep0)
  simpa [show 2 * (1249 * 1) = 1249 * 2 by ring] using h

lemma hU2 : S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 4) - U2 := by
  have h := dvd_sq_step (a := 1249 * 2) (U := U1) (V := U2) (Q := Qustep1) hU1 (by
    simpa [Austep1, Bustep1, Nustep1, U1, U2] using ustep1)
  simpa [show 2 * (1249 * 2) = 1249 * 4 by ring] using h

lemma hU3 : S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 8) - U3 := by
  have h := dvd_sq_step (a := 1249 * 4) (U := U2) (V := U3) (Q := Qustep2) hU2 (by
    simpa [Austep2, Bustep2, Nustep2, U2, U3] using ustep2)
  simpa [show 2 * (1249 * 4) = 1249 * 8 by ring] using h

lemma hU4 : S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 16) - U4 := by
  have h := dvd_sq_step (a := 1249 * 8) (U := U3) (V := U4) (Q := Qustep3) hU3 (by
    simpa [Austep3, Bustep3, Nustep3, U3, U4] using ustep3)
  simpa [show 2 * (1249 * 8) = 1249 * 16 by ring] using h

lemma hU5 : S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 32) - U5 := by
  have h := dvd_sq_step (a := 1249 * 16) (U := U4) (V := U5) (Q := Qustep4) hU4 (by
    simpa [Austep4, Bustep4, Nustep4, U4, U5] using ustep4)
  simpa [show 2 * (1249 * 16) = 1249 * 32 by ring] using h

lemma hU6 : S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 64) - U6 := by
  have h := dvd_sq_step (a := 1249 * 32) (U := U5) (V := U6) (Q := Qustep5) hU5 (by
    simpa [Austep5, Bustep5, Nustep5, U5, U6] using ustep5)
  simpa [show 2 * (1249 * 32) = 1249 * 64 by ring] using h

lemma hU7 : S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 128) - U7 := by
  have h := dvd_sq_step (a := 1249 * 64) (U := U6) (V := U7) (Q := Qustep6) hU6 (by
    simpa [Austep6, Bustep6, Nustep6, U6, U7] using ustep6)
  simpa [show 2 * (1249 * 64) = 1249 * 128 by ring] using h

lemma hU8 : S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 256) - U8 := by
  have h := dvd_sq_step (a := 1249 * 128) (U := U7) (V := U8) (Q := Qustep7) hU7 (by
    simpa [Austep7, Bustep7, Nustep7, U7, U8] using ustep7)
  simpa [show 2 * (1249 * 128) = 1249 * 256 by ring] using h

lemma hU9 : S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 512) - U9 := by
  have h := dvd_sq_step (a := 1249 * 256) (U := U8) (V := U9) (Q := Qustep8) hU8 (by
    simpa [Austep8, Bustep8, Nustep8, U8, U9] using ustep8)
  simpa [show 2 * (1249 * 256) = 1249 * 512 by ring] using h

lemma hU10 : S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1024) - U10 := by
  have h := dvd_sq_step (a := 1249 * 512) (U := U9) (V := U10) (Q := Qustep9) hU9 (by
    simpa [Austep9, Bustep9, Nustep9, U9, U10] using ustep9)
  simpa [show 2 * (1249 * 512) = 1249 * 1024 by ring] using h

theorem chain1249sqU : S2550F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1024) - U10 := hU10

end LeanFormal.IUT.XiFPaper.S2593aUChainActual

end