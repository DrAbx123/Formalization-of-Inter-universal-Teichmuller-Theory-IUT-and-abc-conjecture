import Mathlib

/-!
# Mzk1MuNTorsionV2Actual — nth roots of unity as a subgroup of units (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
Closure of nth roots of unity in the unit group of C under one/mul/inv (genuine Mathlib facts). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1MuNTorsionV2Actual

/-- Genuine theorem: one is an nth root of unity. -/
theorem one_mem_rootsOfUnity (n : ℕ) :
    (1 : ℂˣ) ∈ rootsOfUnity n ℂ :=
  (rootsOfUnity n ℂ).one_mem

/-- Genuine theorem: product of nth roots of unity is an nth root of unity. -/
theorem mul_mem_rootsOfUnity (n : ℕ) {a b : ℂˣ}
    (ha : a ∈ rootsOfUnity n ℂ) (hb : b ∈ rootsOfUnity n ℂ) :
    a * b ∈ rootsOfUnity n ℂ :=
  (rootsOfUnity n ℂ).mul_mem ha hb

/-- Genuine theorem: inverse of an nth root of unity is an nth root of unity. -/
theorem inv_mem_rootsOfUnity (n : ℕ) {a : ℂˣ}
    (ha : a ∈ rootsOfUnity n ℂ) : a⁻¹ ∈ rootsOfUnity n ℂ :=
  (rootsOfUnity n ℂ).inv_mem ha

end LeanFormal.IUT.XiFPaper.Mzk1MuNTorsionV2Actual
