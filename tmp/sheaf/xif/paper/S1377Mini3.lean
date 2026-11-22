import Mathlib.NumberTheory.EllipticDivisibilitySequence

variable {R : Type*} [CommRing R] (W : ℤ → R)

section Perm
variable (hneg : ∀ k, W (-k) = -W k)

lemma testneg (m : ℤ) : W (-m) = -W m := hneg m

lemma testneg2 (m n : ℤ) : W (-m) + W (-n) = -W m + -W n := by
  rw [hneg m, hneg n]

end Perm
