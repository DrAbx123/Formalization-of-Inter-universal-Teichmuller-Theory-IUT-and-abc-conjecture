import Mathlib.Tactic
open Polynomial

example : (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
  rw [show (2 : ZMod 5) * 2 = -1 by decide]
  simp only [Polynomial.C_neg, Polynomial.C_1]
  ring

example : (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
  ext n
  simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow,
    Polynomial.coeff_sub, Polynomial.coeff_mul, Polynomial.coeff_X, Polynomial.coeff_C]
  split_ifs <;> decide

example : (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
  have h : (2 : ZMod 5) * 2 = -1 := by decide
  calc (X^2 + 1 : (ZMod 5)[X]) = X^2 - C ((2 : ZMod 5) * 2) := by
        rw [h]; simp
    _ = (X - C 2) * (X + C 2) := by ring

example : (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
  have h : (2 : ZMod 5) * 2 = -1 := by decide
  rw [h]
  ring_nf
