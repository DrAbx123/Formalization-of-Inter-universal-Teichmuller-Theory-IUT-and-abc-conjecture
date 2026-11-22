import Mathlib
variable {α : Type*} [DecidableEq α] (s : Multiset α)
#synth Fintype {x // x ∈ s}
example : (Finset.univ : Finset {x // x ∈ s}).val = s.attach := by
  rfl
