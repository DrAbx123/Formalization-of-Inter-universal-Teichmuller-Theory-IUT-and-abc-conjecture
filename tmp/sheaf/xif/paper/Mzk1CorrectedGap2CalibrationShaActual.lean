import Mathlib.Tactic

/-! # Gap2 object-level calibration (theta absorption) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap2CalibrationShaActual

/-- Gap2 with explicit theta is equivalent to Gap2 with theta absorbed in D. -/
theorem corrected_gap2_theta_absorption_iff {v w : Nat → Nat → Nat → Real} {theta : Real}
    {P : Nat → Nat → Nat → Prop} :
    (∀ epsilon : Real, 0 < epsilon → ∃ D : Real,
      ∀ a b c : Nat, P a b c → v a b c ≤ (1 + epsilon) * w a b c + theta + D)
      ↔
    (∀ epsilon : Real, 0 < epsilon → ∃ D : Real,
      ∀ a b c : Nat, P a b c → v a b c - theta ≤ (1 + epsilon) * w a b c + D) := by
  constructor
  · intro h epsilon hepsilon
    obtain ⟨D, hD⟩ := h epsilon hepsilon
    exact ⟨D, fun a b c habc => by linarith [hD a b c habc]⟩
  · intro h epsilon hepsilon
    obtain ⟨D, hD⟩ := h epsilon hepsilon
    exact ⟨D, fun a b c habc => by linarith [hD a b c habc]⟩

/-- Numeric calibration: `v=1, w=0, theta=1, P=True` satisfies both forms with `D=0`. -/
theorem corrected_gap2_numeric_calibration :
    ∃ (v w : Nat → Nat → Nat → Real) (theta : Real) (P : Nat → Nat → Nat → Prop),
      (∀ epsilon : Real, 0 < epsilon → ∃ D : Real,
        ∀ a b c : Nat, P a b c → v a b c ≤ (1 + epsilon) * w a b c + theta + D) ∧
      (∀ epsilon : Real, 0 < epsilon → ∃ D : Real,
        ∀ a b c : Nat, P a b c → v a b c - theta ≤ (1 + epsilon) * w a b c + D) := by
  refine ⟨fun _ _ _ => 1, fun _ _ _ => 0, 1, fun _ _ _ => True, ?_, ?_⟩
  · intro epsilon hepsilon
    exact ⟨(0 : Real), fun a b c _ => by norm_num⟩
  · intro epsilon hepsilon
    exact ⟨(0 : Real), fun a b c _ => by norm_num⟩

#print axioms corrected_gap2_theta_absorption_iff
#print axioms corrected_gap2_numeric_calibration

end LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap2CalibrationShaActual
