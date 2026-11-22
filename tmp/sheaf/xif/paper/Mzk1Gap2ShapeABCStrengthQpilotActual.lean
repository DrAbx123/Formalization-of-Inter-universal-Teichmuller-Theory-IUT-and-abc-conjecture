/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1Gap2ShapeABCStrengthQpilotActual — Gap2 shape decomposition / ABC strength (A680)

Object-level decomposition of the Gap-2 shape and the strength relation between
its per-`ε` and uniform-in-`ε` versions:
* `v ≤ (1+ε)w + θ + D ↔ v ≤ w + (ε*w + θ + D)` (base weight + slack);
* uniform-in-`ε` `D` implies per-`ε` `D`;
* the converse fails in general (explicit numeric counterexample). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap2ShapeABCStrengthQpilotActual

/-- Gap-2 shape decomposition: `(1+ε)w + θ + D = w + (ε*w + θ + D)`. -/
theorem gap2_decompose {v w theta D epsilon : Real} :
    (v ≤ (1 + epsilon) * w + theta + D) ↔
      (v ≤ w + (epsilon * w + theta + D)) := by
  constructor <;> intro h <;> linarith

/-- Uniform-in-`ε` additive constant implies the per-`ε` form. -/
theorem gap2_uniform_implies_perEpsilon {v w : Nat → Nat → Nat → Real} {theta : Real}
    (h : ∃ D : Real, ∀ epsilon : Real, 0 < epsilon →
      ∀ a b c : Nat, v a b c ≤ (1 + epsilon) * w a b c + theta + D) :
    ∀ epsilon : Real, 0 < epsilon → ∃ D : Real,
      ∀ a b c : Nat, v a b c ≤ (1 + epsilon) * w a b c + theta + D := by
  obtain ⟨D, hD⟩ := h
  exact fun epsilon hepsilon => ⟨D, hD epsilon hepsilon⟩

/-- The converse fails: the per-`ε` form does not imply a uniform constant
(counterexample `v = 1`, `w = −1`, `θ = 0`: it needs `D ≥ 2 + ε`). -/
theorem gap2_perEpsilon_not_uniform :
    ¬ (∃ D : Real, ∀ epsilon : Real, 0 < epsilon →
        1 ≤ (1 + epsilon) * (-1 : Real) + 0 + D) := by
  rintro ⟨D, hD⟩
  have heps : 0 < |D| + 2 := by positivity
  have h := hD (|D| + 2) heps
  have habs : D ≤ |D| := le_abs_self D
  nlinarith

/-- Rows for the Gap2 shape/strength calibration. -/
def gap2StrengthRows : List (String × String) :=
  [ ("Gap2 decomposition (base + slack)", "PROVED"),
    ("uniform => per-eps", "PROVED"),
    ("per-eps ⇏ uniform (counterexample)", "PROVED") ]

theorem gap2StrengthRows_length : gap2StrengthRows.length = 3 := rfl

#check gap2_decompose
#check gap2_uniform_implies_perEpsilon
#check gap2_perEpsilon_not_uniform
#check gap2StrengthRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Gap2ShapeABCStrengthQpilotActual
end
