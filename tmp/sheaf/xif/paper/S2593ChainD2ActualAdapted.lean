import tmp.sheaf.xif.paper.S2590Q1249ChainActual
import tmp.sheaf.xif.paper.S2561Batch2CorrectActual
import tmp.sheaf.xif.paper.S2562Batch3CorrectActual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual
open LeanFormal.IUT.XiFPaper.S2561Batch2CorrectActual
open LeanFormal.IUT.XiFPaper.S2562Batch3CorrectActual
open LeanFormal.IUT.XiFPaper.S2590Q1249ChainActual
namespace LeanFormal.IUT.XiFPaper.S2593ChainD2ActualAdapted
abbrev F : (ZMod 1249)[X] := S2550F10
private lemma dvd_mul_shift {a a' b b' : (ZMod 1249)[X]}
    (ha : F ∣ a - a') (hb : F ∣ b - b') : F ∣ a * b - a' * b' := by
  have h : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [h]
  exact dvd_add (dvd_mul_of_dvd_left ha b) (dvd_mul_of_dvd_right hb a')
private lemma dvd_sq_step {P R S Q : (ZMod 1249)[X]}
    (hdiv : F ∣ P - R) (hstep : R * R = F * Q + S) : F ∣ P * P - S := by
  have h1 : F ∣ (P - R) * (P + R) := dvd_mul_of_dvd_left hdiv _
  have h2 : F ∣ R * R - S := by
    refine ⟨Q, ?_⟩
    rw [hstep]; ring
  have h : P * P - S = (P - R) * (P + R) + (R * R - S) := by ring
  rw [h]
  exact dvd_add h1 h2
def U : Nat → (ZMod 1249)[X]
  | 0 => S2561Batch2CorrectActual.U0
  | 1 => S2561Batch2CorrectActual.U1
  | 2 => S2561Batch2CorrectActual.U2
  | 3 => S2561Batch2CorrectActual.U3
  | 4 => S2561Batch2CorrectActual.U4
  | 5 => S2561Batch2CorrectActual.U5
  | 6 => S2561Batch2CorrectActual.U6
  | 7 => S2561Batch2CorrectActual.U7
  | 8 => S2561Batch2CorrectActual.U8
  | 9 => S2561Batch2CorrectActual.U9
  | 10 => S2561Batch2CorrectActual.U10
  | _ => 0
def Qu : Nat → (ZMod 1249)[X]
  | 0 => S2561Batch2CorrectActual.Qustep0
  | 1 => S2561Batch2CorrectActual.Qustep1
  | 2 => S2561Batch2CorrectActual.Qustep2
  | 3 => S2561Batch2CorrectActual.Qustep3
  | 4 => S2561Batch2CorrectActual.Qustep4
  | 5 => S2561Batch2CorrectActual.Qustep5
  | 6 => S2561Batch2CorrectActual.Qustep6
  | 7 => S2561Batch2CorrectActual.Qustep7
  | 8 => S2561Batch2CorrectActual.Qustep8
  | 9 => S2561Batch2CorrectActual.Qustep9
  | _ => 0
private lemma ustep (k : Nat) (hk : k < 10) : U k * U k = F * Qu k + U (k + 1) := by
  interval_cases k <;>
    simp [U, Qu, F, S2561Batch2CorrectActual.ustep0, S2561Batch2CorrectActual.ustep1,
      S2561Batch2CorrectActual.ustep2, S2561Batch2CorrectActual.ustep3,
      S2561Batch2CorrectActual.ustep4, S2561Batch2CorrectActual.ustep5,
      S2561Batch2CorrectActual.ustep6, S2561Batch2CorrectActual.ustep7,
      S2561Batch2CorrectActual.ustep8, S2561Batch2CorrectActual.ustep9]
theorem chainU (k : Nat) (hk : k ≤ 10) :
    F ∣ ((X : (ZMod 1249)[X]) ^ 1249) ^ (2 ^ k) - U k := by
  induction k with
  | zero =>
      simpa [U] using (S2590Q1249ChainActual.chain1249)
  | succ k ih =>
      have hk9 : k ≤ 9 := by omega
      have hk10 : k ≤ 10 := by omega
      have hstep := ustep k (by omega)
      have h := dvd_sq_step (P := ((X : (ZMod 1249)[X]) ^ 1249) ^ (2 ^ k)) ih hstep
      simpa [U, Qu, pow_two, pow_mul, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h
theorem chainD2 : F ∣ (X : (ZMod 1249)[X]) ^ (1249 * 1249) - V4 := by
  have h1024 : F ∣ ((X : (ZMod 1249)[X]) ^ 1249) ^ 1024 - U 10 := chainU 10 (by norm_num)
  have h128 : F ∣ ((X : (ZMod 1249)[X]) ^ 1249) ^ 128 - U 7 := chainU 7 (by norm_num)
  have h64 : F ∣ ((X : (ZMod 1249)[X]) ^ 1249) ^ 64 - U 6 := chainU 6 (by norm_num)
  have h32 : F ∣ ((X : (ZMod 1249)[X]) ^ 1249) ^ 32 - U 5 := chainU 5 (by norm_num)
  have h1 : F ∣ ((X : (ZMod 1249)[X]) ^ 1249) ^ 1024 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 128 - U 10 * U 7 :=
    dvd_mul_shift h1024 h128
  have hprod0 : F ∣ U 10 * U 7 - V1 := by
    have h := S2562Batch3CorrectActual.vstep0
    refine ⟨S2562Batch3CorrectActual.Qvstep0, ?_⟩
    simpa [U, F, S2562Batch3CorrectActual.Avstep0, S2562Batch3CorrectActual.Bvstep0,
      S2562Batch3CorrectActual.Nvstep0] using h
  have h2 : F ∣ ((X : (ZMod 1249)[X]) ^ 1249) ^ 1024 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 128 - V1 := by
    have h := dvd_add h1 hprod0
    convert h using 1 <;> ring
  have hshift1 : F ∣ ((X : (ZMod 1249)[X]) ^ 1249) ^ 1024 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 128 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 64 - V1 * U 6 :=
    dvd_mul_shift h2 h64
  have hprod1 : F ∣ V1 * U 6 - V2 := by
    have h := S2562Batch3CorrectActual.vstep1
    refine ⟨S2562Batch3CorrectActual.Qvstep1, ?_⟩
    simpa [U, F, S2562Batch3CorrectActual.Avstep1, S2562Batch3CorrectActual.Bvstep1,
      S2562Batch3CorrectActual.Nvstep1] using h
  have h3 : F ∣ ((X : (ZMod 1249)[X]) ^ 1249) ^ 1024 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 128 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 64 - V2 := by
    have h := dvd_add hshift1 hprod1
    convert h using 1 <;> ring
  have hshift2 : F ∣ ((X : (ZMod 1249)[X]) ^ 1249) ^ 1024 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 128 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 64 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 32 - V2 * U 5 :=
    dvd_mul_shift h3 h32
  have hprod2 : F ∣ V2 * U 5 - V3 := by
    have h := S2562Batch3CorrectActual.vstep2
    refine ⟨S2562Batch3CorrectActual.Qvstep2, ?_⟩
    simpa [U, F, S2562Batch3CorrectActual.Avstep2, S2562Batch3CorrectActual.Bvstep2,
      S2562Batch3CorrectActual.Nvstep2] using h
  have h4 : F ∣ ((X : (ZMod 1249)[X]) ^ 1249) ^ 1024 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 128 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 64 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 32 - V3 := by
    have h := dvd_add hshift2 hprod2
    convert h using 1 <;> ring
  have h1x : F ∣ ((X : (ZMod 1249)[X]) ^ 1249) ^ 1 - U 0 := chainU 0 (by norm_num)
  have hshift3 : F ∣ ((X : (ZMod 1249)[X]) ^ 1249) ^ 1024 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 128 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 64 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 32 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 1 - V3 * U 0 :=
    dvd_mul_shift h4 h1x
  have hprod3 : F ∣ V3 * U 0 - V4 := by
    have h := S2562Batch3CorrectActual.vstep3
    refine ⟨S2562Batch3CorrectActual.Qvstep3, ?_⟩
    simpa [U, F, S2562Batch3CorrectActual.Avstep3, S2562Batch3CorrectActual.Bvstep3,
      S2562Batch3CorrectActual.Nvstep3] using h
  have h5 : F ∣ ((X : (ZMod 1249)[X]) ^ 1249) ^ 1024 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 128 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 64 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 32 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 1 - V4 := by
    have h := dvd_add hshift3 hprod3
    convert h using 1 <;> ring
  have hpow : ((X : (ZMod 1249)[X]) ^ 1249) ^ 1024 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 128 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 64 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 32 * ((X : (ZMod 1249)[X]) ^ 1249) ^ 1 =
      (X : (ZMod 1249)[X]) ^ (1249 * 1249) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  simpa [hpow] using h5
#check chainD2
end LeanFormal.IUT.XiFPaper.S2593ChainD2ActualAdapted
end
