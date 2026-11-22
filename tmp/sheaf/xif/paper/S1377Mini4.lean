import Mathlib.NumberTheory.EllipticDivisibilitySequence

section Test
variable (n : ℕ)
variable (h : n = n)

lemma foo : n = n := h
end Test

section Test2
variable {R : Type*} [CommRing R] (W : ℤ → R)
variable (hW : W 1 = 1)
lemma bar : W 1 = 1 := hW
end Test2
