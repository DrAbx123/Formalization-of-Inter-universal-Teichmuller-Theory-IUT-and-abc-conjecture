import Mathlib.Tactic

/-! # Full-ratio Gap1/Gap2 characterizations + scaling element audit -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GapFullRatioShaActual

/-- Scaling element of the paper region: `a + b + c + 1`. -/
def scalingElement (a b c : Nat) : Nat := a + b + c + 1

theorem scalingElement_pos (a b c : Nat) : 0 < scalingElement a b c := by
  unfold scalingElement
  omega

/-- Gap 1 at full ratio (`ε → 0`) is exactly the pointwise height bound. -/
theorem gap1_full_ratio_iff (h L : Real) (hL : 0 ≤ L) :
    (forall epsilon : Real, 0 < epsilon → h ≤ (1 + epsilon) * L) ↔ h ≤ L := by
  constructor
  · intro H
    refine le_of_forall_pos_le_add ?_
    intro epsilon heps
    have hL1 : 0 < L + 1 := by linarith
    have heps' : 0 < epsilon / (L + 1) := div_pos heps hL1
    have hb := H (epsilon / (L + 1)) heps'
    have hfac : (epsilon / (L + 1)) * L ≤ epsilon := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hL1]
      nlinarith [hL]
    linarith
  · intro hLe epsilon heps
    have heps0 : 0 ≤ epsilon := le_of_lt heps
    nlinarith

/-- Gap 2 at full ratio (`ε → 0`) is exactly the pointwise volume bound with
a fixed `D` (weight nonnegative). -/
theorem gap2_full_ratio_iff (v w theta : Real) (hw : 0 ≤ w) :
    (forall epsilon : Real, 0 < epsilon → exists D : Real,
      v ≤ (1 + epsilon) * w + theta + D) ↔
    exists D : Real, v ≤ w + theta + D := by
  constructor
  · intro H
    obtain ⟨D, hD⟩ := H 1 (by norm_num)
    refine ⟨D + w, ?_⟩
    nlinarith
  · rintro ⟨D, hD⟩ epsilon heps
    refine ⟨D, ?_⟩
    have heps0 : 0 ≤ epsilon := le_of_lt heps
    nlinarith [mul_nonneg heps0 hw]

#print axioms gap1_full_ratio_iff
#print axioms gap2_full_ratio_iff
#print axioms scalingElement_pos

end LeanFormal.IUT.XiFPaper.Mzk1GapFullRatioShaActual
