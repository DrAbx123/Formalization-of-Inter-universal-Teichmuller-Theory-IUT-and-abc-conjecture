import Mathlib.Tactic
open Polynomial

example : (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
  have h : (4 : ZMod 5) = -1 := by decide
  calc (X^2 + 1 : (ZMod 5)[X]) = X^2 - C 4 := by
        rw [h]
        simp
    _ = (X - C 2) * (X + C 2) :=
        (show (X - C 2) * (X + C 2) = X^2 - C 4 by ring_nf).symm

example : (X^2 + 1 : (ZMod 5)[X]).Splits := by
  have hfac : (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
    have h : (4 : ZMod 5) = -1 := by decide
    calc (X^2 + 1 : (ZMod 5)[X]) = X^2 - C 4 := by rw [h]; simp
      _ = (X - C 2) * (X + C 2) :=
          (show (X - C 2) * (X + C 2) = X^2 - C 4 by ring_nf).symm
  rw [hfac]
  exact (Polynomial.Splits.X_sub_C 2).mul (Polynomial.Splits.X_add_C 2)
