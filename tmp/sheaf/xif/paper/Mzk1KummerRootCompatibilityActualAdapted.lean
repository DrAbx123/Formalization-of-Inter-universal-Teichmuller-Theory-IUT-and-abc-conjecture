/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Kummer theory: compatibility of n-th roots via roots of unity -/

namespace LeanFormal.IUT.XiFPaper.KummerRootCompatibilityActual

variable {K : Type*} [Field K]

/-- An n-th root datum for a unit a: a chosen unit r with r^n = a. -/
structure KummerRoot (K : Type*) [Field K] (n : Nat) (a : Kˣ) where
  root : Kˣ
  pow_eq : root ^ n = a

/-- Two n-th roots of the same unit differ by an n-th root of unity. -/
theorem kummerRoot_ratio_mem_rootsOfUnity {n : Nat} {a : Kˣ}
    (r s : KummerRoot K n a) :
    r.root / s.root ∈ rootsOfUnity n K := by
  rw [mem_rootsOfUnity]
  rw [div_pow, r.pow_eq, s.pow_eq]
  exact div_self (a := a) (Units.ext rfl |>.symm ▸ (by simp))

/-- Conversely, an n-th root of unity converts one n-th root into another. -/
theorem kummerRoot_mul_rootsOfUnity {n : Nat} {a : Kˣ} (r : KummerRoot K n a)
    (zeta : Kˣ) (hz : zeta ∈ rootsOfUnity n K) :
    (r.root * zeta) ^ n = a := by
  rw [mul_pow, r.pow_eq, mem_rootsOfUnity.mp hz]
  simp

end LeanFormal.IUT.XiFPaper.KummerRootCompatibilityActual
