/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # mu_N: roots-of-unity torsion facts (IUT I/II Kummer pre-object) -/

namespace LeanFormal.IUT.XiFPaper.RootsOfUnityFactsActual

variable {K : Type*} [Field K]

/-- n-th roots of unity are closed under multiplication (subgroup fact, restated). -/
theorem mem_rootsOfUnity_mul {n : Nat} {a b : Kˣ}
    (ha : a ∈ rootsOfUnity n K) (hb : b ∈ rootsOfUnity n K) :
    a * b ∈ rootsOfUnity n K :=
  (rootsOfUnity n K).mul_mem ha hb

/-- The n-th roots of unity are contained in the m-th roots when n divides m. -/
theorem rootsOfUnity_le_of_dvd {n m : Nat} (h : n ∣ m) :
    rootsOfUnity n K ≤ rootsOfUnity m K := by
  intro z hz
  rw [mem_rootsOfUnity] at hz ⊢
  obtain ⟨k, rfl⟩ := h
  rw [pow_mul, hz, one_pow]

/-- Membership criterion for the n-th roots of unity (restated). -/
theorem rootsOfUnity_mem_iff {n : Nat} (z : Kˣ) :
    z ∈ rootsOfUnity n K ↔ z ^ n = 1 := mem_rootsOfUnity

end LeanFormal.IUT.XiFPaper.RootsOfUnityFactsActual
