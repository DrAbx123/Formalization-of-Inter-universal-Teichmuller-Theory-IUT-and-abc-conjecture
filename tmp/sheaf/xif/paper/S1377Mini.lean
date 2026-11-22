import Mathlib.NumberTheory.EllipticDivisibilitySequence
open scoped nonZeroDivisors

variable {R : Type*} [CommRing R]
variable (W : ℤ → R)

section Test
variable {a c₀ d₀ : ℤ}
variable (par : c₀ % 2 = d₀ % 2)
variable (mem : W 1 ∈ R⁰)

theorem test (b : ℤ) : True := by
  trivial

theorem test2 (b : ℤ) : W 1 ∈ R⁰ := mem
end Test
