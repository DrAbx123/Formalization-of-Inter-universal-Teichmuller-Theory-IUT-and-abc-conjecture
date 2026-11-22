import Mathlib

/-!
Pure logical probe for the xi-e/xi-f boundary.

This file does not model IUT objects.  It separates the fixed-q
executability condition from the output-readout coverage needed by the
Corollary 3.12 scalar step.
-/

namespace LeanFormal.IUT.N8Closure.XiESourceConditionLogic

def OutputSet (P : Set ℝ) : Prop := P.Nonempty

def FixedQExecutable (_Q : ℝ) (P : Set ℝ) : Prop := OutputSet P

theorem q_le_h_of_exact_coverage {Q h : ℝ} {P : Set ℝ}
    (upper : ∀ x, x ∈ P → x ≤ h) (coverage : Q ∈ P) : Q ≤ h := by
  exact upper Q coverage

theorem q_le_h_of_signed_coverage {Q h : ℝ} {P : Set ℝ}
    (upper : ∀ x, x ∈ P → x ≤ h)
    (coverage : ∀ ε : ℝ, 0 < ε → ∃ x ∈ P, Q - ε ≤ x) : Q ≤ h := by
  by_contra hQ
  have hlt : h < Q := lt_of_not_ge hQ
  let ε : ℝ := (Q - h) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨x, hxP, hxQ⟩ := coverage ε hε
  have hxH : x ≤ h := upper x hxP
  dsimp [ε] at hxQ
  linarith

theorem fixed_q_executability_does_not_imply_coverage :
    ∃ (Q h : ℝ) (P : Set ℝ),
      FixedQExecutable Q P ∧ (∀ x, x ∈ P → x ≤ h) ∧ Q ∉ P := by
  refine ⟨1, 0, ({0} : Set ℝ), ?_, ?_, ?_⟩
  · exact ⟨0, by simp⟩
  · intro x hx
    have hx0 : x = 0 := by simpa using hx
    simp [hx0]
  · norm_num

end LeanFormal.IUT.N8Closure.XiESourceConditionLogic
