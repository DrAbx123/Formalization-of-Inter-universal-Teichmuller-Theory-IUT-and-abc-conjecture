/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1KummerRootCompatibilityActual

/-! # Kummer: chain — two n-th roots differ by an n-th root of unity -/

namespace LeanFormal.IUT.XiFPaper.KummerRootCompatibilityActual

variable {K : Type*} [Field K]

theorem kummerRoot_eq_mul_rootsOfUnity {n : Nat} {a : Kˣ}
    (r s : KummerRoot K n a) :
    ∃ zeta ∈ rootsOfUnity n K, r.root = s.root * zeta := by
  refine ⟨r.root / s.root, kummerRoot_ratio_mem_rootsOfUnity r s, ?_⟩
  group

theorem kummerRoot_eq_mul_rootsOfUnity_unique {n : Nat} {a : Kˣ}
    (r s : KummerRoot K n a) :
    ∃! zeta : Kˣ, zeta ∈ rootsOfUnity n K ∧ r.root = s.root * zeta := by
  obtain ⟨zeta, hz, hEq⟩ := kummerRoot_eq_mul_rootsOfUnity r s
  refine ⟨zeta, ⟨hz, hEq⟩, ?_⟩
  rintro zeta' ⟨_, hEq'⟩
  have hcancel : s.root * zeta' = s.root * zeta := by rw [← hEq', hEq]
  exact mul_left_cancel hcancel

end LeanFormal.IUT.XiFPaper.KummerRootCompatibilityActual
