/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1GraphAutTranslationUnicityActual

/-! # Reuse: corollaries of translation-parameter uniqueness -/

namespace LeanFormal.IUT

theorem graphAut_translation_unique' (sigma : Equiv.Perm Int)
    (h : FrobeniusPictureGraphAut sigma) :
    ExistsUnique (fun k : Int => sigma = chainTranslation k) :=
  graphAut_translation_unique sigma h

theorem chainTranslation_eq_iff_symm (k l : Int) :
    chainTranslation k = chainTranslation l ↔ l = k := by
  rw [chainTranslation_eq_iff, eq_comm]

theorem chainTranslation_injective' : Function.Injective chainTranslation :=
  chainTranslation_injective_param

theorem chainTranslation_eq_one_iff' (k : Int) :
    chainTranslation k = (1 : Equiv.Perm Int) ↔ k = 0 := 
  chainTranslation_eq_one_iff k

theorem chainTranslation_ne_one_iff' (k : Int) :
    chainTranslation k ≠ (1 : Equiv.Perm Int) ↔ k ≠ 0 := 
  chainTranslation_ne_one_iff k

theorem graphAut_translation_param (sigma : Equiv.Perm Int)
    (h : FrobeniusPictureGraphAut sigma) :
    ∃ k : Int, sigma = chainTranslation k := by
  obtain ⟨k, hk, _⟩ := graphAut_translation_unique' sigma h
  exact ⟨k, hk⟩

end LeanFormal.IUT
