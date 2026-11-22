import Mathlib.NumberTheory.EllipticDivisibilitySequence

variable {R : Type*} [CommRing R] (W : ℤ → R)

section Perm
variable (neg : ∀ k, W (-k) = -W k)

lemma testneg (m : ℤ) : W (-m) = -W m := neg m

lemma testneg2 (m n : ℤ) : W (-m) + W (-n) = -W m + -W n := by
  rw [neg m, neg n]

end Perm
