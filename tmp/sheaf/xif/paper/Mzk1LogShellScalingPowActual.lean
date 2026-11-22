/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Log-shell scaling: power bookkeeping for (p*)^-1 normalization -/

namespace LeanFormal.IUT.XiFPaper.LogShellScalingPowActual

/-- The log-shell scaling factor p^n. -/
def lsScale (p : Nat) (n : Nat) : Nat := p ^ n

@[simp] theorem lsScale_zero (p : Nat) : lsScale p 0 = 1 := rfl

@[simp] theorem lsScale_succ (p n : Nat) : lsScale p (n + 1) = lsScale p n * p := by
  simp [lsScale, pow_succ]

theorem lsScale_add (p m n : Nat) : lsScale p (m + n) = lsScale p m * lsScale p n := by
  simp [lsScale, pow_add]

theorem lsScale_mono {p : Nat} (hp : 1 ≤ p) {m n : Nat} (h : m ≤ n) :
    lsScale p m ≤ lsScale p n := by
  unfold lsScale
  exact Nat.pow_le_pow_right hp h

theorem lsScale_pos {p : Nat} (hp : 0 < p) (n : Nat) : 0 < lsScale p n := by
  unfold lsScale
  exact Nat.pow_pos hp n

theorem lsScale_ne_zero {p : Nat} (hp : 0 < p) (n : Nat) : lsScale p n ≠ 0 := 
  Nat.pos_iff_ne_zero.mp (lsScale_pos hp n)

end LeanFormal.IUT.XiFPaper.LogShellScalingPowActual
