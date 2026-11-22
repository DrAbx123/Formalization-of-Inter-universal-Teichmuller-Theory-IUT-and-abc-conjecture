import tmp.sheaf.xif.paper.S2560Batch1CorrectActual

noncomputable section
set_option maxHeartbeats 8000000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual

namespace LeanFormal.IUT.XiFPaper.S2593D2ChainActual

lemma dvd_square_step {A N Q : (ZMod 1249)[X]} (n : ℕ)
    (hA : S2550F10 ∣ X ^ n - A)
    (hstep : A * A = S2550F10 * Q + N) :
    S2550F10 ∣ X ^ (2 * n) - N := by
  obtain ⟨u, hu⟩ := hA
  refine ⟨Q + 2 * A * u + S2550F10 * u * u, ?_⟩
  have hAX : X ^ n = A + S2550F10 * u := by
    rw [add_comm, ← sub_eq_iff_eq_add]
    exact hu
  rw [show X ^ (2 * n) = (X ^ n) ^ 2 by rw [pow_mul]; ring]
  rw [hAX]
  rw [show (A + S2550F10 * u) ^ 2 = A * A + S2550F10 * (2 * A * u + S2550F10 * u * u) by ring]
  rw [hstep]
  ring

lemma dvd_mul_step {A B N Q : (ZMod 1249)[X]} (a b : ℕ)
    (hA : S2550F10 ∣ X ^ a - A)
    (hB : S2550F10 ∣ X ^ b - B)
    (hstep : A * B = S2550F10 * Q + N) :
    S2550F10 ∣ X ^ (a + b) - N := by
  obtain ⟨u, hu⟩ := hA
  obtain ⟨v, hv⟩ := hB
  refine ⟨Q + A * v + B * u + S2550F10 * u * v, ?_⟩
  have hAX : X ^ a = A + S2550F10 * u := by
    rw [add_comm, ← sub_eq_iff_eq_add]
    exact hu
  have hBX : X ^ b = B + S2550F10 * v := by
    rw [add_comm, ← sub_eq_iff_eq_add]
    exact hv
  rw [pow_add, hAX, hBX]
  rw [show (A + S2550F10 * u) * (B + S2550F10 * v) =
      A * B + S2550F10 * (A * v + B * u + S2550F10 * u * v) by ring]
  rw [hstep]
  ring

theorem chain0 : S2550F10 ∣ X ^ (2 ^ 0) - S2560Batch1CorrectActual.R0 := by
  have h : S2560Batch1CorrectActual.R0 = X := by
    unfold S2560Batch1CorrectActual.R0
    simp
  rw [h]
  norm_num

theorem chain1 : S2550F10 ∣ X ^ (2 ^ 1) - S2560Batch1CorrectActual.R1 := by
  rw [show 2 ^ 1 = 2 * 2 ^ 0 by norm_num]
  exact dvd_square_step (2 ^ 0) chain0 S2560Batch1CorrectActual.step0

theorem chain2 : S2550F10 ∣ X ^ (2 ^ 2) - S2560Batch1CorrectActual.R2 := by
  rw [show 2 ^ 2 = 2 * 2 ^ 1 by ring]
  exact dvd_square_step (2 ^ 1) chain1 S2560Batch1CorrectActual.step1

theorem chain3 : S2550F10 ∣ X ^ (2 ^ 3) - S2560Batch1CorrectActual.R3 := by
  rw [show 2 ^ 3 = 2 * 2 ^ 2 by ring]
  exact dvd_square_step (2 ^ 2) chain2 S2560Batch1CorrectActual.step2

theorem chain4 : S2550F10 ∣ X ^ (2 ^ 4) - S2560Batch1CorrectActual.R4 := by
  rw [show 2 ^ 4 = 2 * 2 ^ 3 by ring]
  exact dvd_square_step (2 ^ 3) chain3 S2560Batch1CorrectActual.step3

theorem chain5 : S2550F10 ∣ X ^ (2 ^ 5) - S2560Batch1CorrectActual.R5 := by
  rw [show 2 ^ 5 = 2 * 2 ^ 4 by ring]
  exact dvd_square_step (2 ^ 4) chain4 S2560Batch1CorrectActual.step4

theorem chain6 : S2550F10 ∣ X ^ (2 ^ 6) - S2560Batch1CorrectActual.R6 := by
  rw [show 2 ^ 6 = 2 * 2 ^ 5 by ring]
  exact dvd_square_step (2 ^ 5) chain5 S2560Batch1CorrectActual.step5

theorem chain7 : S2550F10 ∣ X ^ (2 ^ 7) - S2560Batch1CorrectActual.R7 := by
  rw [show 2 ^ 7 = 2 * 2 ^ 6 by ring]
  exact dvd_square_step (2 ^ 6) chain6 S2560Batch1CorrectActual.step6

theorem chain8 : S2550F10 ∣ X ^ (2 ^ 8) - S2560Batch1CorrectActual.R8 := by
  rw [show 2 ^ 8 = 2 * 2 ^ 7 by ring]
  exact dvd_square_step (2 ^ 7) chain7 S2560Batch1CorrectActual.step7

theorem chain9 : S2550F10 ∣ X ^ (2 ^ 9) - S2560Batch1CorrectActual.R9 := by
  rw [show 2 ^ 9 = 2 * 2 ^ 8 by ring]
  exact dvd_square_step (2 ^ 8) chain8 S2560Batch1CorrectActual.step8

theorem chain10 : S2550F10 ∣ X ^ (2 ^ 10) - S2560Batch1CorrectActual.R10 := by
  rw [show 2 ^ 10 = 2 * 2 ^ 9 by ring]
  exact dvd_square_step (2 ^ 9) chain9 S2560Batch1CorrectActual.step9

end LeanFormal.IUT.XiFPaper.S2593D2ChainActual

end