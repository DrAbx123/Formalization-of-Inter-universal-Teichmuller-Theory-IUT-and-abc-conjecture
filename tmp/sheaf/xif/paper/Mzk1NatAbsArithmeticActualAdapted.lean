/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Cor 3.12: integer natAbs arithmetic -/

namespace LeanFormal.IUT.XiFPaper.NatAbsArithmeticActual

variable {a : Int}

theorem natAbs_eq' : (a.natAbs : Int) = a ∨ (a.natAbs : Int) = -a := Int.natAbs_eq a

theorem natAbs_ofNat' (n : Nat) : (n : Int).natAbs = n := Int.natAbs_ofNat n

theorem natAbs_neg_ofNat' (n : Nat) : (-(n : Int)).natAbs = n := by
  simp

theorem natAbs_nonneg' : 0 ≤ a.natAbs := Int.natAbs_nonneg a

theorem natAbs_eq_self {n : Nat} : (n : Int).natAbs = n := natAbs_ofNat' n

theorem natAbs_zero' : (0 : Int).natAbs = 0 := rfl

theorem natAbs_one' : (1 : Int).natAbs = 1 := rfl

end LeanFormal.IUT.XiFPaper.NatAbsArithmeticActual
