import Mathlib

noncomputable section
open Polynomial

def f : (ZMod 29)[X] :=
  C 10 + C 24 * X + C 16 * X^2 + C 14 * X^3 + C 24 * X^4 + C 8 * X^5 +
  C 5 * X^6 + C 7 * X^7 + C 0 * X^8 + C 25 * X^9 + X^10

example : f.Monic := by
  unfold f
  compute_degree!
  done

example : f.natDegree = 10 := by
  unfold f
  compute_degree!

example : f = (C (10 : ZMod 29) - C 5 * X - C 13 * X^2 + C 14 * X^3 - C 5 * X^4 + C 8 * X^5 + C 5 * X^6 + C 7 * X^7 - C 4 * X^9 + X^10) := by
  unfold f
  norm_num
  ring
