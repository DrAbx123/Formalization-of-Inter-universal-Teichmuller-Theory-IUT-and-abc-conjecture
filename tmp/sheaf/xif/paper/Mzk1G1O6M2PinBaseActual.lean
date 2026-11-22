/- O6 P3 base case: the finite-beta base of the general branch pinning. REUSE:
- `Mzk1BetaAvoidingFoldActual.BetaAvoidingAt` / `CV01` / `betaAvoiding_all` (DONE, fold base),
- `Mzk1Consumer24AdapterUnconditionalActual.finiteBetaCorrectedBase_proved` (consumer form),
- `Mzk1G1O6M2PinTerminalBridgeActual` (terminal sets have degree-one members, this lane).
DEDUP: no M2-shaped (complex-valued) base interface existed in the tree. -/
import tmp.sheaf.xif.paper.Mzk1BetaAvoidingFoldActual
import tmp.sheaf.xif.paper.Mzk1G1O6M2PinTerminalBridgeActual
import tmp.sheaf.xif.paper.Mzk1G1PsiM2AnalyticActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinBaseActual
open LeanFormal.IUT.XiFPaper.Mzk1BetaAvoidingFoldActual
open LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinTerminalBridgeActual

/-- The base datum for the pinning recursion: a polynomial of positive degree with values in
`{0,1}` on a finite rational set, critical values in `{0,1}`, and value at `β` avoiding `{0,1}`.
-/
def PinBaseData (S : Finset ℚ) (β : ℚ) : Prop :=
  ∃ q : ℚ[X], 0 < q.natDegree ∧ (∀ s ∈ S, q.eval s = 0 ∨ q.eval s = 1) ∧
    CV01 q ∧ q.eval β ≠ 0 ∧ q.eval β ≠ 1

/-- The finite-beta fold supplies the base datum (donor reuse). -/
theorem pinBaseData_of (S : Finset ℚ) (β : ℚ) (hβ : β ∉ S) : PinBaseData S β := by
  obtain ⟨q, hdeg, hpres, h0, h1, hcv⟩ := betaAvoiding_all S β hβ
  exact ⟨q, hdeg, hpres, hcv, h0, h1⟩

/-- **M2-shaped base case**: the base datum gives a polynomial whose complex values on `S`
and at critical points lie in `{0,1}`, and whose value at `β` avoids `{0,1}`. -/
theorem m2Base_of_pinBaseData (S : Finset ℚ) (β : ℚ) (h : PinBaseData S β) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ S, Polynomial.aeval (algebraMap ℚ ℂ s) q ∈ ({0, 1} : Set ℂ)) ∧
      (∀ z : ℂ, Polynomial.aeval z (Polynomial.derivative q) = 0 →
        Polynomial.aeval z q ∈ ({0, 1} : Set ℂ)) ∧
      Polynomial.aeval (algebraMap ℚ ℂ β) q ∉ ({0, 1} : Set ℂ) := by
  obtain ⟨q, hdeg, hpres, hcv, h0, h1⟩ := h
  refine ⟨q, hdeg, ?_, ?_, ?_⟩
  · intro s hs
    have hval := hpres s hs
    have hae : Polynomial.aeval (algebraMap ℚ ℂ s) q = algebraMap ℚ ℂ (q.eval s) :=
      Polynomial.aeval_algebraMap_apply
    rw [hae]
    rcases hval with h0' | h1'
    · rw [h0']; simp
    · rw [h1']; simp
  · intro z hz
    have := hcv z hz
    rcases this with hzz | hzz
    · simp [hzz]
    · simp [hzz]
  · intro hmem
    have hae : Polynomial.aeval (algebraMap ℚ ℂ β) q = algebraMap ℚ ℂ (q.eval β) :=
      Polynomial.aeval_algebraMap_apply
    rw [hae] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with hz | ho
    · exact h0 (by exact_mod_cast hz)
    · exact h1 (by exact_mod_cast ho)

#print axioms pinBaseData_of
#print axioms m2Base_of_pinBaseData
end LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinBaseActual
