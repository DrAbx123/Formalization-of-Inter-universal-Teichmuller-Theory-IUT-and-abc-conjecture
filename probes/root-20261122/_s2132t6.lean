import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Eval.Defs
open Polynomial
noncomputable section

#check @Polynomial.eval₂_natCast
#check @Polynomial.eval_natCast
#check @Polynomial.eval₂_intCast
#check @Polynomial.eval₂_ofNat
#check @Polynomial.eval₂_at_intCast

example : ((3814697265625 : ℤ[X])).eval₂ (Int.castRingHom ℚ) (3:ℚ) = (3814697265625 : ℚ) := by
  rw [Polynomial.eval₂_natCast]

example : ((3814697265625 : ℤ[X])).eval₂ (Int.castRingHom ℚ) (3:ℚ) = (3814697265625 : ℚ) := by
  simp

example : ((C (3814697265625 : ℤ) : ℤ[X])).eval₂ (Int.castRingHom ℚ) (3:ℚ) = (3814697265625 : ℚ) := by
  simp
