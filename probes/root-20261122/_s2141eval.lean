import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
open Polynomial
noncomputable def PZmod : (ZMod 29)[X] :=
  C 16 + C 21 * X^2 + C 21 * X^3 + C 15 * X^4 + C 1 * X^5 + C 6 * X^6 + C 24 * X^7 + C 14 * X^8 + C 10 * X^9 + C 10 * X^10 + C 8 * X^11 + C 4 * X^12
noncomputable def F2 : (ZMod 29)[X] := C (12 : ZMod 29) + C 6 * X + X^2
noncomputable def F10 : (ZMod 29)[X] := C 10 - C 5 * X - C 13 * X^2 + C 14 * X^3 - C 5 * X^4 + C 8 * X^5 + C 5 * X^6 + C 7 * X^7 - C 4 * X^9 + X^10
example (x : ZMod 29) : (F2 * F10).eval x = PZmod.eval x := by
  simp [F2, F10, PZmod]
  norm_num
