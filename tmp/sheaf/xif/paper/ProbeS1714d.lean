import Mathlib.Tactic
open Polynomial

example : (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
  simp only [Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_neg,
    Polynomial.C_pow, Polynomial.C_ofNat, Polynomial.C_1, Polynomial.C_0]
  ring_nf
  trace_state
  sorry
