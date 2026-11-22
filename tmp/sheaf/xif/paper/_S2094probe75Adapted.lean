import Mathlib
example (d : ℕ) (hdvd : d ∣ 10) (hlt : d < 10) (hpos : 0 < d) : d = 1 ∨ d = 2 ∨ d = 5 := by
  interval_cases d <;> norm_num at hdvd ⊢
