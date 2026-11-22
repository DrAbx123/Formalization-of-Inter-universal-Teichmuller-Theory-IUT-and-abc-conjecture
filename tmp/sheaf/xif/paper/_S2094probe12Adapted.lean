import Mathlib

open Polynomial

local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

noncomputable section
set_option maxRecDepth 10000

def f : (ZMod 29)[X] :=
  C 10 + C 24 * X + C 16 * X^2 + C 14 * X^3 + C 24 * X^4 + C 8 * X^5 +
  C 5 * X^6 + C 7 * X^7 + C 0 * X^8 + C 25 * X^9 + C 1 * X^10

def P1 : (ZMod 29)[X] :=
  C 13 + C 1 * X + C 26 * X^2 + C 24 * X^3 + C 4 * X^4 + C 10 * X^5 +
  C 25 * X^6 + C 23 * X^7 + C 18 * X^8 + C 20 * X^9

example : f ∣ X^29 - P1 := by
  decide
