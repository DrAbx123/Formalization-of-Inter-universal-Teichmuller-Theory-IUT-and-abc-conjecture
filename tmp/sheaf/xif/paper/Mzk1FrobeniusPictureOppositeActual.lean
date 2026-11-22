/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Frobenius-picture Gamma: opposite oriented graph arrows -/

namespace LeanFormal.IUT.XiFPaper.FrobeniusPictureOppositeActual

/-- The opposite arrow relation: n --> m in the opposite graph iff m + 1 = n. -/
def gammaArrowOp (n m : Int) : Prop := m + 1 = n

theorem gammaArrowOp_iff (n m : Int) : gammaArrowOp n m ↔ m + 1 = n := Iff.rfl

theorem gammaArrowOp_irrefl (n : Int) : ¬ gammaArrowOp n n := by
  unfold gammaArrowOp
  omega

theorem gammaArrowOp_functional {n m1 m2 : Int}
    (h1 : gammaArrowOp n m1) (h2 : gammaArrowOp n m2) : m1 = m2 := by
  unfold gammaArrowOp at h1 h2
  omega

theorem gammaArrowOp_comp {n1 n2 n3 : Int}
    (h1 : gammaArrowOp n1 n2) (h2 : gammaArrowOp n2 n3) : n3 + 2 = n1 := by
  unfold gammaArrowOp at h1 h2
  omega

theorem gammaArrowOp_opposite (n m : Int) : gammaArrowOp m n ↔ m + 1 = n := Iff.rfl

end LeanFormal.IUT.XiFPaper.FrobeniusPictureOppositeActual
