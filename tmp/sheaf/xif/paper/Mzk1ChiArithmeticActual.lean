/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Initial Theta: orbifold Euler-characteristic integer arithmetic -/

namespace LeanFormal.IUT.XiFPaper.ChiArithmeticActual

/-- Orbifold Euler characteristic 2 - 2g - n as an integer. -/
def chiInt (g n : Nat) : Int := 2 - 2 * (g : Int) - (n : Int)

theorem chiInt_zero_zero : chiInt 0 0 = 2 := by
  unfold chiInt
  norm_num

theorem chiInt_typeOneOne : chiInt 1 1 = -1 := by
  unfold chiInt
  norm_num

theorem chiInt_add_puncture (g n : Nat) :
    chiInt g (n + 1) = chiInt g n - 1 := by
  unfold chiInt
  push_cast
  ring

theorem chiInt_add_genus (g n : Nat) :
    chiInt (g + 1) n = chiInt g n - 2 := by
  unfold chiInt
  push_cast
  ring

theorem chiInt_nonpos_of_large {g n : Nat}
    (h : (3 : Int) ≤ 2 * (g : Int) + (n : Int)) : chiInt g n ≤ -1 := by
  unfold chiInt
  omega

end LeanFormal.IUT.XiFPaper.ChiArithmeticActual
