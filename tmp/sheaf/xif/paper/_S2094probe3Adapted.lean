import Mathlib

open Polynomial

def f : (ZMod 29)[X] :=
  C 10 + C 24 * X + C 16 * X^2 + C 14 * X^3 + C 24 * X^4 + C 8 * X^5 +
  C 5 * X^6 + C 7 * X^7 + C 0 * X^8 + C 25 * X^9 + C 1 * X^10

example : f.Monic := by
  decide

example : f.natDegree = 10 := by
  decide

example : f.leadingCoeff = 1 := by
  decide
