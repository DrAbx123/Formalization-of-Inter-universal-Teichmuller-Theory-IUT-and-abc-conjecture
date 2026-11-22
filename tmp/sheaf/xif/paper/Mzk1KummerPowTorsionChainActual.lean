/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1KummerRootChainActual
import tmp.sheaf.xif.paper.Mzk1MuNBridgeChainActual

/-! # Chain: Kummer root differences lie in the power-torsion kernel -/

namespace LeanFormal.IUT.XiFPaper.KummerRootCompatibilityActual

open LeanFormal.IUT.XiFPaper.ThetaPowerKernelGenericActual

variable {K : Type*} [Field K]

theorem kummerRoot_ratio_mem_powTorsion {n : Nat} {a : Kˣ}
    (r s : KummerRoot K n a) :
    r.root / s.root ∈ powTorsion (Kˣ) n := by
  rw [← LeanFormal.IUT.XiFPaper.MuNBridgeChainActual.rootsOfUnity_eq_powTorsion K n]
  exact kummerRoot_ratio_mem_rootsOfUnity r s

theorem kummerRoot_eq_mul_powTorsion_unique {n : Nat} {a : Kˣ}
    (r s : KummerRoot K n a) :
    ∃! zeta : Kˣ, zeta ∈ powTorsion (Kˣ) n ∧ r.root = s.root * zeta := by
  obtain ⟨zeta, hz, hEq⟩ := kummerRoot_eq_mul_rootsOfUnity r s
  have hzPow : zeta ∈ powTorsion (Kˣ) n := by
    rw [← LeanFormal.IUT.XiFPaper.MuNBridgeChainActual.rootsOfUnity_eq_powTorsion K n]
    exact hz
  refine ⟨zeta, ⟨hzPow, hEq⟩, ?_⟩
  rintro zeta' ⟨_, hEq'⟩
  have hcancel : s.root * zeta' = s.root * zeta := by rw [← hEq', hEq]
  exact mul_left_cancel hcancel

end LeanFormal.IUT.XiFPaper.KummerRootCompatibilityActual
