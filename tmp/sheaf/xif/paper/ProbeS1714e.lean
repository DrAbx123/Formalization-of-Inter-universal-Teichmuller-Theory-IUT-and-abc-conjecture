import Mathlib.Tactic
open Polynomial

example : (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
  simp only [Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_neg,
    Polynomial.C_pow, Polynomial.C_ofNat, Polynomial.C_1, Polynomial.C_0]
  ring_nf
  rw [show (-4 : ZMod 5) = 1 by decide]
  ring

example : (X^2 + 1 : (ZMod 5)[X]).Splits := by
  have hfac : (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
    simp only [Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_neg,
      Polynomial.C_pow, Polynomial.C_ofNat, Polynomial.C_1, Polynomial.C_0]
    ring_nf
    rw [show (-4 : ZMod 5) = 1 by decide]
    ring
  rw [hfac]
  exact (Polynomial.Splits.X_sub_C 2).mul (Polynomial.Splits.X_add_C 2)
