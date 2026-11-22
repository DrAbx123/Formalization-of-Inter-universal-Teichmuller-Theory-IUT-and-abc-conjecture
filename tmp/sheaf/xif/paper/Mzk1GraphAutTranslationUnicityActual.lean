/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.HodgeTheater.SourceThetaLinkGraphAutomorphismReduction

/-! # Frobenius-picture graph: uniqueness of the translation parameter -/

namespace LeanFormal.IUT

theorem chainTranslation_eq_iff (k l : Int) :
    chainTranslation k = chainTranslation l ↔ k = l := by
  constructor
  · intro h
    exact chainTranslation_injective h
  · intro h
    rw [h]

theorem chainTranslation_eq_one_iff (k : Int) :
    chainTranslation k = (1 : Equiv.Perm Int) ↔ k = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun e : Equiv.Perm Int => e 0) h
    simp [chainTranslation_apply] at h0
    omega
  · rintro rfl
    ext n
    simp [chainTranslation_apply]

theorem graphAut_translation_unique (sigma : Equiv.Perm Int)
    (h : FrobeniusPictureGraphAut sigma) :
    ExistsUnique (fun k : Int => sigma = chainTranslation k) := by
  obtain ⟨k, hk⟩ := (graphAut_eq_translation sigma).mp h
  refine ⟨k, hk, ?_⟩
  intro l hl
  have hkl : chainTranslation k = chainTranslation l := hk.symm.trans hl
  exact ((chainTranslation_eq_iff k l).mp hkl).symm

theorem chainTranslation_injective_param : Function.Injective chainTranslation :=
  chainTranslation_injective

theorem chainTranslation_ne_one_iff (k : Int) :
    chainTranslation k ≠ (1 : Equiv.Perm Int) ↔ k ≠ 0 := not_congr (chainTranslation_eq_one_iff k)

end LeanFormal.IUT

-- force-fresh-recompile
