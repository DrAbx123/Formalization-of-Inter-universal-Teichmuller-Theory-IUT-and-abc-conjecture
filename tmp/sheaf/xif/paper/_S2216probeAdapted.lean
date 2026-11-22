import Mathlib
open Polynomial
example : Irreducible ((X : (ZMod 29)[X])^2 + C 6 * X + C 12) := by
  haveI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : ((X : (ZMod 29)[X])^2 + C 6 * X + C 12).natDegree = 2 := by compute_degree!
    rw [hdeg]
    norm_num
  · have hnot : ∀ x : ZMod 29, x^2 + 6*x + 12 ≠ 0 := by decide +revert
    intro x hx
    exact hnot x (by simpa [IsRoot] using hx)
