import Mathlib.Tactic

noncomputable section
open Polynomial

namespace Prob2132d

noncomputable def PZ : ℤ[X] :=
  3814697265625 + 97656250000000 * X^2 +
    (-133437500000000) * X^3 + (-50580000000000) * X^4 +
    165057216000000 * X^5 + 96445440000000 * X^6 +
    (-89948160000000) * X^7 + (-27525120000000) * X^8 +
    (-10234101760000) * X^9 + (-7322650804224) * X^10 +
    1309965025280 * X^11 + 343597383680 * X^12

noncomputable def F2Z : ℤ[X] := 48 + 24 * X + 4 * X^2

noncomputable def F10Z : ℤ[X] :=
  10 - 5 * X - 13 * X^2 + 14 * X^3 - 5 * X^4 + 8 * X^5 + 5 * X^6 + 7 * X^7 - 4 * X^9 + X^10

noncomputable def QZ : ℤ[X] :=
  131541285005 + 3367456896576 * X^2 +
    (-4601293103460) * X^3 + (-1744137931036) * X^4 +
    5691628137920 * X^5 + 3325704827572 * X^6 +
    (-3101660689672) * X^7 + (-949142068972) * X^8 +
    (-352900060684) * X^9 + (-252505200144) * X^10 +
    45171207768 * X^11 + 11848185644 * X^12

theorem integer_identity : PZ = F2Z * F10Z + 29 * QZ := by
  unfold PZ F2Z F10Z QZ
  ring

theorem product_map :
    F2Z.map (Int.castRingHom (ZMod 29)) * F10Z.map (Int.castRingHom (ZMod 29)) =
      PZ.map (Int.castRingHom (ZMod 29)) := by
  have h := congrArg (Polynomial.map (Int.castRingHom (ZMod 29))) integer_identity
  simp only [Polynomial.map_add, Polynomial.map_mul] at h
  rw [h]
  simp

end Prob2132d
