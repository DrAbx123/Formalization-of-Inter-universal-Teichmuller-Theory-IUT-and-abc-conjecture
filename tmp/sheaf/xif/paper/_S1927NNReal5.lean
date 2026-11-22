import Mathlib.Data.NNReal.Basic

example (a b : NNReal) (h : a + b = 0) : a = 0 := by
  have hle : a ≤ 0 := by
    have h' : a ≤ a + b := le_add_right le_rfl
    rwa [h] at h'
  exact le_antisymm hle zero_le
