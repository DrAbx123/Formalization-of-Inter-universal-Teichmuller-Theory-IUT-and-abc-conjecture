import tmp.sheaf.xif.paper.S2582PowerTwoChainAltActual
import tmp.sheaf.xif.paper.S2561Batch2CorrectActual
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual
open LeanFormal.IUT.XiFPaper.S2561Batch2CorrectActual

namespace LeanFormal.IUT.XiFPaper.S2583X1249CertificateActual

abbrev F : (ZMod 1249)[X] := S2550F10

theorem dvd_mul_sub {A a B b : (ZMod 1249)[X]}
    (hA : F ∣ A - a) (hB : F ∣ B - b) : F ∣ A * B - a * b := by
  have h : A * B - a * b = (A - a) * B + a * (B - b) := by ring
  rw [h]
  exact dvd_add (dvd_mul_of_dvd_right hA B) (dvd_mul_of_dvd_left hB a)

theorem tstep0_dvd : F ∣ T0 * S2560Batch1CorrectActual.R7 - T1 := by
  have h := S2561Batch2CorrectActual.tstep0
  refine ⟨Qtstep0, ?_⟩
  have h' : Atstep0 * Btstep0 - Ntstep0 = F * Qtstep0 := by
    rw [h]; ring
  simpa [Atstep0, Btstep0, Ntstep0, T0, T1, F] using h'

theorem tstep1_dvd : F ∣ T1 * S2560Batch1CorrectActual.R6 - T2 := by
  have h := S2561Batch2CorrectActual.tstep1
  refine ⟨Qtstep1, ?_⟩
  have h' : Atstep1 * Btstep1 - Ntstep1 = F * Qtstep1 := by
    rw [h]; ring
  simpa [Atstep1, Btstep1, Ntstep1, T1, T2, F] using h'

theorem tstep2_dvd : F ∣ T2 * S2560Batch1CorrectActual.R5 - T3 := by
  have h := S2561Batch2CorrectActual.tstep2
  refine ⟨Qtstep2, ?_⟩
  have h' : Atstep2 * Btstep2 - Ntstep2 = F * Qtstep2 := by
    rw [h]; ring
  simpa [Atstep2, Btstep2, Ntstep2, T2, T3, F] using h'

theorem tstep3_dvd : F ∣ T3 * S2560Batch1CorrectActual.R0 - T4 := by
  have h := S2561Batch2CorrectActual.tstep3
  refine ⟨Qtstep3, ?_⟩
  have h' : Atstep3 * Btstep3 - Ntstep3 = F * Qtstep3 := by
    rw [h]; ring
  simpa [Atstep3, Btstep3, Ntstep3, T3, T4, F] using h'

theorem xpow_eq : (X : (ZMod 1249)[X]) ^ 1024 * X ^ 128 * X ^ 64 * X ^ 32 * X =
    (X : (ZMod 1249)[X]) ^ 1249 := by
  rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
  norm_num

theorem X1249_remainder_dvd : F ∣ (X : (ZMod 1249)[X]) ^ 1249 - T4 := by
  have h1024 : F ∣ (X : (ZMod 1249)[X]) ^ 1024 - R10 := S2582PowerTwoChainAltActual.chain 10 (by norm_num)
  have h128 : F ∣ (X : (ZMod 1249)[X]) ^ 128 - R7 := S2582PowerTwoChainAltActual.chain 7 (by norm_num)
  have h64 : F ∣ (X : (ZMod 1249)[X]) ^ 64 - R6 := S2582PowerTwoChainAltActual.chain 6 (by norm_num)
  have h32 : F ∣ (X : (ZMod 1249)[X]) ^ 32 - R5 := S2582PowerTwoChainAltActual.chain 5 (by norm_num)
  have h1 : F ∣ (X : (ZMod 1249)[X]) ^ 1 - R0 := S2582PowerTwoChainAltActual.chain 0 (by norm_num)
  have hp1 : F ∣ (X : (ZMod 1249)[X]) ^ 1024 * X ^ 128 - R10 * R7 :=
    dvd_mul_sub h1024 h128
  have hp2 : F ∣ (X : (ZMod 1249)[X]) ^ 1024 * X ^ 128 * X ^ 64 - R10 * R7 * R6 :=
    dvd_mul_sub hp1 h64
  have hp3 : F ∣ (X : (ZMod 1249)[X]) ^ 1024 * X ^ 128 * X ^ 64 * X ^ 32 -
      R10 * R7 * R6 * R5 := dvd_mul_sub hp2 h32
  have hp4 : F ∣ (X : (ZMod 1249)[X]) ^ 1024 * X ^ 128 * X ^ 64 * X ^ 32 * X -
      R10 * R7 * R6 * R5 * R0 := dvd_mul_sub hp3 h1
  have hp4' : F ∣ (X : (ZMod 1249)[X]) ^ 1249 - R10 * R7 * R6 * R5 * R0 := by
    convert hp4 using 1
    exact xpow_eq.symm
  have hba : F ∣ R10 * R7 - T0 * R7 := by
    simpa [T0] using tstep0_dvd.neg_right
  -- start from T0 and multiply by R6, R5, R0
  have hb0 : F ∣ T0 * R7 - T1 := tstep0_dvd
  have hb0' : F ∣ T0 * R7 * R6 - T1 * R6 :=
    dvd_mul_of_dvd_right hb0 R6
  have hb1 : F ∣ T1 * R6 - T2 := tstep1_dvd
  have hb01 : F ∣ T0 * R7 * R6 - T2 := by
    have := dvd_add hb0' hb1
    convert this using 1 <;> ring
  have hb01' : F ∣ T0 * R7 * R6 * R5 - T2 * R5 :=
    dvd_mul_of_dvd_right hb01 R5
  have hb2 : F ∣ T2 * R5 - T3 := tstep2_dvd
  have hb012 : F ∣ T0 * R7 * R6 * R5 - T3 := by
    have := dvd_add hb01' hb2
    convert this using 1 <;> ring
  have hb012' : F ∣ T0 * R7 * R6 * R5 * R0 - T3 * R0 :=
    dvd_mul_of_dvd_right hb012 R0
  have hb3 : F ∣ T3 * R0 - T4 := tstep3_dvd
  have hball : F ∣ T0 * R7 * R6 * R5 * R0 - T4 := by
    have := dvd_add hb012' hb3
    convert this using 1 <;> ring
  have hball' : F ∣ R10 * R7 * R6 * R5 * R0 - T4 := by
    simpa [T0] using hball
  have := dvd_add hp4' hball'
  convert this using 1 <;> ring

noncomputable def Q1249 : (ZMod 1249)[X] := (X : (ZMod 1249)[X]) ^ 1249 / F

theorem X1249_expanded :
    (X : (ZMod 1249)[X]) ^ 1249 = F * Q1249 + T4 := by
  have hFdeg : F.degree = 10 := by unfold F S2550F10; compute_degree!
  have hTdeg : T4.degree ≤ 9 := by unfold T4; compute_degree!
  have hF0 : F ≠ 0 := by
    intro h
    rw [h] at hFdeg
    simp at hFdeg
  have hTmod : T4 % F = T4 := by
    apply (Polynomial.mod_eq_self_iff hF0).mpr
    rw [hFdeg]
    exact lt_of_le_of_lt hTdeg (by norm_num)
  have hmod : (X : (ZMod 1249)[X]) ^ 1249 % F = T4 := by
    rw [Polynomial.mod_eq_of_dvd_sub X1249_remainder_dvd, hTmod]
  have h := EuclideanDomain.div_add_mod ((X : (ZMod 1249)[X]) ^ 1249) F
  rw [hmod] at h
  exact h.symm

#check X1249_expanded
#check X1249_remainder_dvd

end LeanFormal.IUT.XiFPaper.S2583X1249CertificateActual
end
