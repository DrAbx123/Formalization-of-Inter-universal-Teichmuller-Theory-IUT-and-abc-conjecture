import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
open Polynomial

example : (7322650804224 : ZMod 29) = 12 := by norm_num
example : (7322650804224 : ZMod 29) = 12 := by decide

noncomputable def PZmod : (ZMod 29)[X] :=
  C 3814697265625 + C 97656250000000 * X^2 + C (-133437500000000) * X^3 +
  C (-50580000000000) * X^4 + C 165057216000000 * X^5 + C 96445440000000 * X^6 +
  C (-89948160000000) * X^7 + C (-27525120000000) * X^8 +
  C (-10234101760000) * X^9 + C (-7322650804224) * X^10 +
  C 1309965025280 * X^11 + C 343597383680 * X^12
noncomputable def F2 : (ZMod 29)[X] := C (12 : ZMod 29) + C 6 * X + X^2
noncomputable def F10 : (ZMod 29)[X] := C 10 - C 5 * X - C 13 * X^2 + C 14 * X^3 - C 5 * X^4 + C 8 * X^5 + C 5 * X^6 + C 7 * X^7 - C 4 * X^9 + X^10

example : F2 * F10 = PZmod := by
  unfold F2 F10 PZmod
  simp only [map_ofNat, map_neg]
  norm_num
  ring_nf

example : F2 * F10 = PZmod := by
  unfold F2 F10 PZmod
  simp only [map_ofNat, map_neg]
  norm_num1
  ring_nf

example (x : ZMod 29) : (F2*F10).eval x = PZmod.eval x := by
  simp [F2, F10, PZmod]
  ring_nf
  norm_num
