import Mathlib.NumberTheory.EllipticDivisibilitySequence

section Test
variable (n : ℕ)
variable (h : n = n)
include h
lemma foo : n = n := h
end Test
