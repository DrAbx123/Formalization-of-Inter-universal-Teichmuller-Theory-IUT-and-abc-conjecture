/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Cor 3.12: integer height arithmetic (natAbs triangle/congruence) -/

namespace LeanFormal.IUT.XiFPaper.HeightArithmeticActual

def height (a : Int) : Nat := a.natAbs

@[simp] theorem height_zero : height 0 = 0 := rfl

theorem height_neg (a : Int) : height (-a) = height a := Int.natAbs_neg a

theorem height_add_le (a b : Int) : height (a + b) ≤ height a + height b :=
  Int.natAbs_add_le a b

theorem height_mul (a b : Int) : height (a * b) = height a * height b :=
  Int.natAbs_mul a b

theorem height_sub_le (a b : Int) : height (a - b) ≤ height a + height b := by
  rw [sub_eq_add_neg, height_add_le]
  rw [height_neg]

theorem height_nonneg (a : Int) : 0 ≤ height a := Nat.zero_le _

theorem height_eq_zero_iff {a : Int} : height a = 0 ↔ a = 0 := by
  unfold height
  exact Int.natAbs_eq_zero

end LeanFormal.IUT.XiFPaper.HeightArithmeticActual
