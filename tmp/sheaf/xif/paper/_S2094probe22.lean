import Mathlib
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section
@[simp] lemma C_natCast_mod (n : ℕ) :
    (C ((n : ℕ) : ZMod 29) : (ZMod 29)[X]) = C (((n % 29 : ℕ) : ZMod 29)) := by
  rw [C_inj, ZMod.natCast_eq_natCast_iff']

example : (C (((24 : ℕ) : ZMod 29)) * C (((7 : ℕ) : ZMod 29)) : (ZMod 29)[X]) = C (((23 : ℕ) : ZMod 29)) := by
  simp only [← C_mul, ← Nat.cast_mul, C_natCast_mod]

example : (X^2 * C (((24 : ℕ) : ZMod 29)) * C (((7 : ℕ) : ZMod 29)) : (ZMod 29)[X]) = C (((23 : ℕ) : ZMod 29)) * X^2 := by
  simp only [mul_assoc]
  simp only [← C_mul, ← Nat.cast_mul, C_natCast_mod]
  ring
