/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P7/#1: target-interface predicates for the comparison chain -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ComparisonTargetInterfaceActual

/-- The target in `M = A - R` form. -/
def MTargetNonneg (A R : ℝ) : Prop := 0 ≤ A - R

/-- Equivalent signed form `-A <= -R`. -/
def SignedTarget (A R : ℝ) : Prop := -A ≤ -R

theorem MTargetNonneg_iff_SignedTarget (A R : ℝ) :
    MTargetNonneg A R ↔ SignedTarget A R := by
  unfold MTargetNonneg SignedTarget
  constructor <;> intro h <;> linarith

theorem MTargetNonneg_iff_R_le_A (A R : ℝ) :
    MTargetNonneg A R ↔ R ≤ A := by
  unfold MTargetNonneg
  constructor <;> intro h <;> linarith

end LeanFormal.IUT.XiFPaper.Mzk1ComparisonTargetInterfaceActual