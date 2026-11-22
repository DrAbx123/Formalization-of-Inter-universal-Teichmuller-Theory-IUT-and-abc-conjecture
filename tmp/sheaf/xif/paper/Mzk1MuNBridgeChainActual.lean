/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib
import tmp.sheaf.xif.paper.Mzk1ThetaPowerKernelGenericActual
import tmp.sheaf.xif.paper.Mzk1RootsOfUnityFactsActual

/-! # mu_N bridge: roots of unity as power-torsion kernels -/

namespace LeanFormal.IUT.XiFPaper.MuNBridgeChainActual

open LeanFormal.IUT.XiFPaper.ThetaPowerKernelGenericActual

variable {K : Type*} [Field K]

/-- The n-th roots of unity are exactly the n-th power-torsion subgroup of Kˣ. -/
theorem rootsOfUnity_eq_powTorsion (K : Type*) [Field K] (n : Nat) :
    rootsOfUnity n K = powTorsion (Kˣ) n := by
  ext z
  rw [mem_rootsOfUnity, mem_powTorsion_iff]

/-- The first roots of unity are trivial. -/
theorem rootsOfUnity_one_eq_bot (K : Type*) [Field K] :
    rootsOfUnity 1 K = ⊥ := by
  rw [rootsOfUnity_eq_powTorsion, powTorsion_one]

/-- Divisibility gives inclusion of roots-of-unity subgroups. -/
theorem rootsOfUnity_le_of_dvd' (K : Type*) [Field K] {n m : Nat} (h : n ∣ m) :
    rootsOfUnity n K ≤ rootsOfUnity m K := by
  intro z hz
  rw [rootsOfUnity_eq_powTorsion] at hz ⊢
  exact powTorsion_le_of_dvd h hz

end LeanFormal.IUT.XiFPaper.MuNBridgeChainActual
