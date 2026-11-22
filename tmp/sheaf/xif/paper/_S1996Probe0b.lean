import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.RingHoms

example (a : ℤ) : ¬ (5 : ℤ) ∣ (1 - 5 * a ^ 2) := by
  intro h
  have h5 : (5 : ℤ) ∣ 5 * a ^ 2 := ⟨a ^ 2, rfl⟩
  have h1 : (5 : ℤ) ∣ 1 := by
    have := dvd_add h h5
    simpa [sub_add_cancel] using this
  norm_num at h1

example (a : ℤ) : ¬ (5 : ℤ) ∣ (1 - 5 * a ^ 2) := by
  omega

example (a : ℤ) : Padic.norm (1 - 5 * a ^ 2 : ℚ_[5]) = 1 := by
  rw [Padic.norm_intCast_eq_one_iff]
  intro h
  have h5 : (5 : ℤ) ∣ 5 * a ^ 2 := ⟨a ^ 2, rfl⟩
  have h1 : (5 : ℤ) ∣ 1 := by
    have := dvd_add h h5
    simpa [sub_add_cancel] using this
  norm_num at h1
