import tmp.sheaf.xif.paper.S2560Batch1CorrectActual

noncomputable section
set_option maxRecDepth 10000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2550TwoFactorCertificateActual
open LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual

namespace LeanFormal.IUT.XiFPaper.S2581PowerTwoChainCorrectActualAdapted

abbrev F10 : (ZMod 1249)[X] := S2550F10

/-- If F10 divides P - R and R^2 = F10*Q + S, then F10 divides P^2 - S. -/
theorem chainStep {P R S Q : (ZMod 1249)[X]}
    (hdiv : F10 ∣ P - R) (hstep : R * R = F10 * Q + S) :
    F10 ∣ P * P - S := by
  have h1 : F10 ∣ (P - R) * (P + R) := dvd_mul_of_dvd_left hdiv _
  have h2 : F10 ∣ R * R - S := by
    refine ⟨Q, ?_⟩
    rw [hstep]
    ring
  have h : P * P - S = (P - R) * (P + R) + (R * R - S) := by ring
  rw [h]
  exact dvd_add h1 h2

theorem chain0 : F10 ∣ (X : (ZMod 1249)[X]) ^ 1 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0 := by
  have h : (X : (ZMod 1249)[X]) ^ 1 = LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0 := by
    unfold LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0
    ring
  rw [h]
  simp

theorem chain1 : F10 ∣ (X : (ZMod 1249)[X]) ^ 2 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R1 := by
  have h := chainStep (P := (X : (ZMod 1249)[X]) ^ 1) (R := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R0) (S := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R1) (Q := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.Q0)
    chain0 step0
  simpa [pow_two] using h

theorem chain2 : F10 ∣ (X : (ZMod 1249)[X]) ^ 4 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R2 := by
  have h := chainStep (P := (X : (ZMod 1249)[X]) ^ 2) (R := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R1) (S := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R2) (Q := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.Q1)
    chain1 step1
  simpa [pow_two, pow_mul] using h

theorem chain3 : F10 ∣ (X : (ZMod 1249)[X]) ^ 8 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R3 := by
  have h := chainStep (P := (X : (ZMod 1249)[X]) ^ 4) (R := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R2) (S := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R3) (Q := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.Q2)
    chain2 step2
  simpa [pow_two, pow_mul] using h

theorem chain4 : F10 ∣ (X : (ZMod 1249)[X]) ^ 16 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R4 := by
  have h := chainStep (P := (X : (ZMod 1249)[X]) ^ 8) (R := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R3) (S := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R4) (Q := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.Q3)
    chain3 step3
  simpa [pow_two, pow_mul] using h

theorem chain5 : F10 ∣ (X : (ZMod 1249)[X]) ^ 32 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R5 := by
  have h := chainStep (P := (X : (ZMod 1249)[X]) ^ 16) (R := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R4) (S := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R5) (Q := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.Q4)
    chain4 step4
  simpa [pow_two, pow_mul] using h

theorem chain6 : F10 ∣ (X : (ZMod 1249)[X]) ^ 64 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R6 := by
  have h := chainStep (P := (X : (ZMod 1249)[X]) ^ 32) (R := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R5) (S := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R6) (Q := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.Q5)
    chain5 step5
  simpa [pow_two, pow_mul] using h

theorem chain7 : F10 ∣ (X : (ZMod 1249)[X]) ^ 128 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7 := by
  have h := chainStep (P := (X : (ZMod 1249)[X]) ^ 64) (R := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R6) (S := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7) (Q := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.Q6)
    chain6 step6
  simpa [pow_two, pow_mul] using h

theorem chain8 : F10 ∣ (X : (ZMod 1249)[X]) ^ 256 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R8 := by
  have h := chainStep (P := (X : (ZMod 1249)[X]) ^ 128) (R := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R7) (S := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R8) (Q := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.Q7)
    chain7 step7
  simpa [pow_two, pow_mul] using h

theorem chain9 : F10 ∣ (X : (ZMod 1249)[X]) ^ 512 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R9 := by
  have h := chainStep (P := (X : (ZMod 1249)[X]) ^ 256) (R := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R8) (S := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R9) (Q := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.Q8)
    chain8 step8
  simpa [pow_two, pow_mul] using h

theorem chain10 : F10 ∣ (X : (ZMod 1249)[X]) ^ 1024 - LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10 := by
  have h := chainStep (P := (X : (ZMod 1249)[X]) ^ 512) (R := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R9) (S := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.R10) (Q := LeanFormal.IUT.XiFPaper.S2560Batch1CorrectActual.Q9)
    chain9 step9
  simpa [pow_two, pow_mul] using h

end LeanFormal.IUT.XiFPaper.S2581PowerTwoChainCorrectActualAdapted
end
