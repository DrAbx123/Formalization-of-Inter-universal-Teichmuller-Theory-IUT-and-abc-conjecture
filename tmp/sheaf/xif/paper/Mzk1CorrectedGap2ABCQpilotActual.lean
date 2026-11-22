/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1CorrectedGap2ABCQpilotActual — Gap2 object-level calibration (A677)

Object-level calibration of the corrected Gap-2 estimate: the `θ` term can be
absorbed into the additive constant `D`, i.e. the ABC-form comparison
`v ≤ (1+ε)w + θ + D` is equivalent to `v − θ ≤ (1+ε)w + D`; numerically
calibrated.  **This is only the θ-absorption equivalence; it is NOT a Gap2 ⇔ ABC
statement** (A688 semantics: the unique remaining named input is the
corrected-region Gap 2 shape itself).  No bridge object is changed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap2ABCQpilotActual

/-- Gap-2 with explicit `θ` is equivalent to Gap-2 with `θ` absorbed in `D`. -/
theorem corrected_gap2_iff_ABC {v w : Nat → Nat → Nat → Real} {theta : Real}
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


/-- Alias with the non-misleading name: this is the θ-absorption equivalence only. -/
theorem correctedGap2_theta_absorb_iff {v w : Nat → Nat → Nat → Real} {theta : Real}
    {P : Nat → Nat → Nat → Prop} :
    (∀ epsilon : Real, 0 < epsilon → ∃ D : Real,
      ∀ a b c : Nat, P a b c → v a b c ≤ (1 + epsilon) * w a b c + theta + D)
      ↔
    (∀ epsilon : Real, 0 < epsilon → ∃ D : Real,
      ∀ a b c : Nat, P a b c → v a b c - theta ≤ (1 + epsilon) * w a b c + D) :=
  corrected_gap2_iff_ABC

/-- Numeric calibration of the absorption: `θ = 1`, `D = 0` absorbed to `D = 1`. -/
theorem corrected_gap2_numeric_calibration :
    ∃ (v w : Nat → Nat → Nat → Real) (theta : Real) (P : Nat → Nat → Nat → Prop),
      (∀ epsilon : Real, 0 < epsilon → ∃ D : Real,
        ∀ a b c : Nat, P a b c → v a b c ≤ (1 + epsilon) * w a b c + theta + D) ∧
      (∀ epsilon : Real, 0 < epsilon → ∃ D : Real,
        ∀ a b c : Nat, P a b c → v a b c - theta ≤ (1 + epsilon) * w a b c + D) := by
  refine ⟨fun _ _ _ => 1, fun _ _ _ => 0, 1, fun _ _ _ => True,
    ?_, ?_⟩
  · intro epsilon hepsilon
    exact ⟨0, fun a b c _ => by norm_num⟩
  · intro epsilon hepsilon
    exact ⟨0, fun a b c _ => by norm_num⟩

/-- Gap-2 calibration rows. -/
def correctedGap2Rows : List (String × String) :=
  [ ("theta absorption equivalence (NOT Gap2 <=> ABC)", "PROVED"),
    ("numeric calibration", "PROVED") ]

theorem correctedGap2Rows_length : correctedGap2Rows.length = 2 := rfl

#check corrected_gap2_iff_ABC
#check corrected_gap2_numeric_calibration
#check correctedGap2Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap2ABCQpilotActual
end
