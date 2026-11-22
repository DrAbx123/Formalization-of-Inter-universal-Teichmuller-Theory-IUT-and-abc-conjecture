import Mathlib
example : (0 : WithBot ℕ) = ⊥ := rfl
example {p : ℚ[X]} (h : p.degree ≠ 0) : p ≠ 0 := by
  intro hp
  apply h
  rw [hp]
  rfl
