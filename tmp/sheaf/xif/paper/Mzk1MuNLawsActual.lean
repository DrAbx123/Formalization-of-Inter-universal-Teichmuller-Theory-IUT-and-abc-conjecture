import Mathlib

/-!
# Mzk1MuNLawsActual — mu_N torsion and roots of unity laws (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Genuine Mathlib facts about roots of unity and torsion subgroups. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1MuNLawsActual

/-- Genuine: powers of a unit root stay roots. -/
theorem rootsOfUnityPow_mem (n : ℕ) [NeZero n] (ζ : ℂ) (h : ζ ∈ rootsOfUnity n ℂ)
    (k : ℕ) : ζ ^ k ∈ rootsOfUnity n ℂ := by
  exact rootsOfUnity.pow_mem h k

/-- Genuine: product of roots of unity is a root of unity. -/
theorem rootsOfUnityMul_mem (n : ℕ) [NeZero n] (ζ η : ℂ)
    (hζ : ζ ∈ rootsOfUnity n ℂ) (hη : η ∈ rootsOfUnity n ℂ) :
    ζ * η ∈ rootsOfUnity n ℂ := by
  exact rootsOfUnity.mul_mem hζ hη

end LeanFormal.IUT.XiFPaper.Mzk1MuNLawsActual
