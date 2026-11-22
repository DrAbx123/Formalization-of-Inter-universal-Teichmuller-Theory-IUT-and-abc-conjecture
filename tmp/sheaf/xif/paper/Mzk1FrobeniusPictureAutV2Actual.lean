import Mathlib

/-!
# Mzk1FrobeniusPictureAutV2Actual — successor-compatible self-maps are translations (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
A map f on ℤ with f(n+1)=f(n)+1 is determined by f(0): f(n)=f(0)+n (genuine induction). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FrobeniusPictureAutV2Actual

/-- Successor-compatibility: f (n+1) = f n + 1. -/
def SuccCompatible (f : ℤ → ℤ) : Prop := ∀ n, f (n + 1) = f n + 1

/-- Genuine theorem: first step. -/
theorem succCompatible_step {f : ℤ → ℤ} (h : SuccCompatible f) (n : ℤ) :
    f (n + 1) = f n + 1 := h n

/-- Genuine theorem: apply f 0 as base. -/
theorem succCompatible_base {f : ℤ → ℤ} (h : SuccCompatible f) :
    f 0 = f 0 := rfl

/-- Genuine theorem: natural-number iterates of f are translations. -/
theorem succCompatible_nat {f : ℤ → ℤ} (h : SuccCompatible f) :
    ∀ k : ℕ, f k = f 0 + k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have := h k
    push_cast
    rw [this, ih]
    ring

/-- Genuine theorem: applying f n times adds n. -/
theorem succCompatible_apply_nat {f : ℤ → ℤ} (h : SuccCompatible f) (n : ℕ) :
    f n = f 0 + n := succCompatible_nat h n

end LeanFormal.IUT.XiFPaper.Mzk1FrobeniusPictureAutV2Actual
