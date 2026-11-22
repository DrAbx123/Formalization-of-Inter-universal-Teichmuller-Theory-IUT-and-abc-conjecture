import tmp.sheaf.xif.paper.S2593bVChainActual
import tmp.sheaf.xif.paper.S2562Batch3CorrectActual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2594aWChainActual
open LeanFormal.IUT.XiFPaper.S2593aUChainActual
open LeanFormal.IUT.XiFPaper.S2593bVChainActual
abbrev F10 : (ZMod 1249)[X] := LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10
lemma dvd_mul_shift {a a' b b' : (ZMod 1249)[X]}
    (ha : F10 ∣ a - a') (hb : F10 ∣ b - b') : F10 ∣ a * b - a' * b' := by
  have h : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [h]
  exact dvd_add (dvd_mul_of_dvd_left ha b) (dvd_mul_of_dvd_right hb a')
lemma dvd_sq_step {a : Nat} {U V Q : (ZMod 1249)[X]}
    (h : F10 ∣ (X : (ZMod 1249)[X]) ^ a - U)
    (hstep : U * U = F10 * Q + V) :
    F10 ∣ (X : (ZMod 1249)[X]) ^ (2 * a) - V := by
  have h1 : F10 ∣ (X : (ZMod 1249)[X]) ^ a * X ^ a - U * U := dvd_mul_shift h h
  have h2 : F10 ∣ U * U - V := by
    rw [hstep]
    simpa [add_sub_cancel_right] using dvd_mul_right F10 Q
  have hsum := dvd_add h1 h2
  have hpow : (X : (ZMod 1249)[X]) ^ (2 * a) = X ^ a * X ^ a := by
    rw [show 2 * a = a + a by omega, pow_add]
  have hEq : (X : (ZMod 1249)[X]) ^ a * X ^ a - V =
      (X ^ a * X ^ a - U * U) + (U * U - V) := by ring
  rw [hpow, hEq]
  exact hsum
lemma W0_eq_V4 : LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W0 = LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.V4 := by
  ext n
  by_cases hn : n ≤ 9
  · interval_cases n <;>
      (simp [LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W0, LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.V4] <;> decide)
  · have h1 : LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W0.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W0.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W0; compute_degree!
      omega
    have h2 : LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.V4.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h : LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.V4.natDegree ≤ 9 := by unfold LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.V4; compute_degree!
      omega
    rw [h1, h2]
lemma hW0 : F10 ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249) - LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W0 := by
  rw [W0_eq_V4]
  exact hV4
lemma hW1 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 2) - LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W1 := by
  have h := dvd_sq_step (a := 1249 * 1249) (U := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W0) (V := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W1) (Q := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep0) hW0 (by
    simpa [LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Awstep0,
      LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Bwstep0,
      LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Nwstep0,
      LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W0,
      LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W1] using LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.wstep0)
  simpa [show 2 * (1249 * 1249) = (1249 * 1249) * 2 by ring] using h
lemma hW2 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 4) - LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W2 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 2) (U := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W1) (V := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W2) (Q := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep1) hW1 (by
    change LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Awstep1 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Bwstep1 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep1 + LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Nwstep1
    exact LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.wstep1)
  simpa [show 2 * (((1249 * 1249) * 2)) = (1249 * 1249) * 4 by ring] using h
lemma hW3 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 8) - LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W3 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 4) (U := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W2) (V := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W3) (Q := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep2) hW2 (by
    change LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Awstep2 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Bwstep2 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep2 + LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Nwstep2
    exact LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.wstep2)
  simpa [show 2 * (((1249 * 1249) * 4)) = (1249 * 1249) * 8 by ring] using h
lemma hW4 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 16) - LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W4 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 8) (U := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W3) (V := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W4) (Q := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep3) hW3 (by
    change LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Awstep3 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Bwstep3 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep3 + LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Nwstep3
    exact LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.wstep3)
  simpa [show 2 * (((1249 * 1249) * 8)) = (1249 * 1249) * 16 by ring] using h
lemma hW5 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 32) - LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W5 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 16) (U := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W4) (V := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W5) (Q := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep4) hW4 (by
    change LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Awstep4 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Bwstep4 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep4 + LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Nwstep4
    exact LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.wstep4)
  simpa [show 2 * (((1249 * 1249) * 16)) = (1249 * 1249) * 32 by ring] using h
lemma hW6 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 64) - LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W6 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 32) (U := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W5) (V := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W6) (Q := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep5) hW5 (by
    change LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Awstep5 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Bwstep5 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep5 + LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Nwstep5
    exact LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.wstep5)
  simpa [show 2 * (((1249 * 1249) * 32)) = (1249 * 1249) * 64 by ring] using h
lemma hW7 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 128) - LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W7 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 64) (U := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W6) (V := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W7) (Q := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep6) hW6 (by
    change LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Awstep6 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Bwstep6 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep6 + LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Nwstep6
    exact LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.wstep6)
  simpa [show 2 * (((1249 * 1249) * 64)) = (1249 * 1249) * 128 by ring] using h
lemma hW8 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 256) - LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W8 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 128) (U := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W7) (V := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W8) (Q := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep7) hW7 (by
    change LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Awstep7 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Bwstep7 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep7 + LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Nwstep7
    exact LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.wstep7)
  simpa [show 2 * (((1249 * 1249) * 128)) = (1249 * 1249) * 256 by ring] using h
lemma hW9 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 512) - LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W9 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 256) (U := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W8) (V := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W9) (Q := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep8) hW8 (by
    change LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Awstep8 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Bwstep8 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep8 + LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Nwstep8
    exact LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.wstep8)
  simpa [show 2 * (((1249 * 1249) * 256)) = (1249 * 1249) * 512 by ring] using h
lemma hW10 : F10 ∣ (X : (ZMod 1249)[X]) ^ ((1249 * 1249) * 1024) - LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W10 := by
  have h := dvd_sq_step (a := (1249 * 1249) * 512) (U := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W9) (V := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.W10) (Q := LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep9) hW9 (by
    change LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Awstep9 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Bwstep9 = LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual.S2550F10 * LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Qwstep9 + LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.Nwstep9
    exact LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual.wstep9)
  simpa [show 2 * (((1249 * 1249) * 512)) = (1249 * 1249) * 1024 by ring] using h
#check hW10
end LeanFormal.IUT.XiFPaper.S2594aWChainActual
end
