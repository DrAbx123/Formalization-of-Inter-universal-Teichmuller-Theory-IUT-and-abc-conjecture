/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic
/-! # Piecewise ceil decomposition for the p-part of torsion -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1CeilDecompActual
/-- Write `m + r = f*k` with `r < f`, `k ≤ A` when `m ≤ f*A`. -/
theorem ceil_decomp
    {f m A : Nat} (hf : 0 < f) (hm : m ≤ f * A) :
    ∃ k r : Nat, m + r = f * k ∧ r < f ∧ k ≤ A := by
  classical
  let q := m / f
  let s := m % f
  have hdecomp : m = f * q + s := by
    dsimp [q, s]
    exact (Nat.div_add_mod m f).symm
  have hsle : s < f := by
    dsimp [s]
    exact Nat.mod_lt m hf
  by_cases hs : s = 0
  · have hmq : m = f * q := by rw [hdecomp, hs, add_zero]
    have hkA : q ≤ A := by
      have : f * q ≤ f * A := by rwa [← hmq]
      exact Nat.le_of_mul_le_mul_left this hf
    refine ⟨q, 0, ?_, hf, hkA⟩
    simpa [hmq]
  · have hs0 : 0 < s := Nat.pos_of_ne_zero hs
    have hlt : f * q < f * A := by
      have hle : f * q + s ≤ f * A := by rwa [← hdecomp]
      omega
    have hqA : q < A := Nat.lt_of_mul_lt_mul_left hlt
    refine ⟨q + 1, f - s, ?_, ?_, by omega⟩
    · have hsub : f - s + s = f := Nat.sub_add_cancel (le_of_lt hsle)
      have h1 : m + (f - s) = f * (q + 1) := by
        rw [hdecomp]
        rw [Nat.mul_add, Nat.mul_one]
        omega
      exact h1
    · omega

/-- Exponent identity for the corrected decomposition. -/
theorem exponent_decomp
    {f m A k r : Nat} (hk : k ≤ A) (hkr : m + r = f * k)
    (hm : m ≤ f * A) :
    f * A - m = f * (A - k) + r := by
  have hfk_le : f * k ≤ f * A := Nat.mul_le_mul_left f hk
  have hmr_le : m + r ≤ f * A := by rwa [hkr]
  have hmul : f * (A - k) = f * A - f * k := Nat.mul_sub_left_distrib f A k
  omega
end LeanFormal.IUT.XiFPaper.Mzk1CeilDecompActual
end