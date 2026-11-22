import tmp.sheaf.xif.paper.S2560Batch1CorrectActual

/-! # S2582: independent power-of-two chain for the F10 remainders

chain0..chain10: `F10 ∣ X^(2^k) - Rk`.  Uses only S2560Batch1CorrectActual
steps and the algebraic identity `P^2 - S = (P-R)(P+R) + (R^2-S)`. -/

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual

namespace LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual

abbrev F : (ZMod 1249)[X] := S2550F10

noncomputable def R : Nat → (ZMod 1249)[X]
  | 0 => R0
  | 1 => R1
  | 2 => R2
  | 3 => R3
  | 4 => R4
  | 5 => R5
  | 6 => R6
  | 7 => R7
  | 8 => R8
  | 9 => R9
  | 10 => R10
  | _ => 0

noncomputable def Q : Nat → (ZMod 1249)[X]
  | 0 => Q0
  | 1 => Q1
  | 2 => Q2
  | 3 => Q3
  | 4 => Q4
  | 5 => Q5
  | 6 => Q6
  | 7 => Q7
  | 8 => Q8
  | 9 => Q9
  | _ => 0

theorem step (k : Nat) (hk : k < 10) :
    R k * R k = F * Q k + R (k + 1) := by
  interval_cases k <;>
    simp [R, Q, F, S2560Batch1CorrectActual.step0,
      S2560Batch1CorrectActual.step1,
      S2560Batch1CorrectActual.step2,
      S2560Batch1CorrectActual.step3,
      S2560Batch1CorrectActual.step4,
      S2560Batch1CorrectActual.step5,
      S2560Batch1CorrectActual.step6,
      S2560Batch1CorrectActual.step7,
      S2560Batch1CorrectActual.step8,
      S2560Batch1CorrectActual.step9]

theorem chain (k : Nat) (hk : k ≤ 10) :
    F ∣ X ^ (2 ^ k) - R k := by
  induction k with
  | zero =>
      refine ⟨0, ?_⟩
      simpa [R, S2560Batch1CorrectActual.R0]
  | succ k ih =>
      have hk9 : k ≤ 9 := by omega
      have hk10 : k ≤ 10 := by omega
      obtain ⟨T, hT⟩ := ih hk10
      have hstep := step k (by omega)
      have hdiff : R k * R k - R (k + 1) = F * Q k := by
        rw [hstep]
        ring
      have hpow : (X : (ZMod 1249)[X]) ^ (2 ^ (k + 1)) =
          ((X : (ZMod 1249)[X]) ^ (2 ^ k)) ^ 2 := by
        have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
          rw [pow_succ]
          ring
        rw [h2, pow_add]
        ring_nf
      refine ⟨T * (X ^ (2 ^ k) + R k) + Q k, ?_⟩
      rw [hpow]
      calc
        (X ^ (2 ^ k)) ^ 2 - R (k + 1)
            = (X ^ (2 ^ k) - R k) * (X ^ (2 ^ k) + R k) +
                (R k * R k - R (k + 1)) := by ring
        _ = (F * T) * (X ^ (2 ^ k) + R k) + (F * Q k) := by
              rw [hT, hdiff]
        _ = F * (T * (X ^ (2 ^ k) + R k) + Q k) := by ring_nf

theorem chain0 : F ∣ X ^ (2 ^ 0) - R 0 := chain 0 (by norm_num)
theorem chain1 : F ∣ X ^ (2 ^ 1) - R 1 := chain 1 (by norm_num)
theorem chain2 : F ∣ X ^ (2 ^ 2) - R 2 := chain 2 (by norm_num)
theorem chain3 : F ∣ X ^ (2 ^ 3) - R 3 := chain 3 (by norm_num)
theorem chain4 : F ∣ X ^ (2 ^ 4) - R 4 := chain 4 (by norm_num)
theorem chain5 : F ∣ X ^ (2 ^ 5) - R 5 := chain 5 (by norm_num)
theorem chain6 : F ∣ X ^ (2 ^ 6) - R 6 := chain 6 (by norm_num)
theorem chain7 : F ∣ X ^ (2 ^ 7) - R 7 := chain 7 (by norm_num)
theorem chain8 : F ∣ X ^ (2 ^ 8) - R 8 := chain 8 (by norm_num)
theorem chain9 : F ∣ X ^ (2 ^ 9) - R 9 := chain 9 (by norm_num)
theorem chain10 : F ∣ X ^ (2 ^ 10) - R 10 := chain 10 (by norm_num)

#check chain
#print axioms chain

end LeanFormal.IUT.XiFPaper.S2582PowerTwoChainAltActual
end
