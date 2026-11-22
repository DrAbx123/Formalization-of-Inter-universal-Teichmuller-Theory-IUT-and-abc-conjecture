import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
open Polynomial
example :
  (C (12 : ZMod 29) + C 6 * X + X^2) *
  (C 10 - C 5 * X - C 13 * X^2 + C 14 * X^3 - C 5 * X^4 + C 8 * X^5 + C 5 * X^6 + C 7 * X^7 + 0 * X^8 - C 4 * X^9 + X^10) =
  (C (12 : ZMod 29) + C 6 * X + X^2) *
  (C 10 - C 5 * X - C 13 * X^2 + C 14 * X^3 - C 5 * X^4 + C 8 * X^5 + C 5 * X^6 + C 7 * X^7 - C 4 * X^9 + X^10) := by ring
