import Mathlib.Tactic
open Polynomial

example : (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
  have h4 : (C (2 : ZMod 5) : (ZMod 5)[X]) ^ 2 = C 4 := by
    rw [← Polynomial.C_pow]
    congr 1
    decide
  have h : (4 : ZMod 5) = -1 := by decide
  rw [show (X - C 2) * (X + C 2) = X^2 - C 4 by
    ring_nf
    rw [h4]]
  rw [h]
  simp

example : (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
  have h : (4 : ZMod 5) = -1 := by decide
  rw [show (X - C 2) * (X + C 2) = X^2 - C 4 by ring_nf]
  rw [h]
  simp
