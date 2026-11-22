import Mathlib.Tactic
open Polynomial

example : (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
  simp only [Polynomial.C_ofNat]
  ring_nf
  congr 1
  decide
