/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.HodgeTheater.SourceThetaLinkGraphAutomorphismReduction

/-! # Reuse: computation corollaries for chain translations (tree asset) -/

namespace LeanFormal.IUT

theorem chainTranslation_apply_zero' (n : Int) : chainTranslation 0 n = n := by
  rw [chainTranslation_apply]
  simp

theorem chainTranslation_apply_one (n : Int) : chainTranslation 1 n = n + 1 := 
  chainTranslation_apply 1 n

theorem chainTranslation_apply_neg (k : Int) (n : Int) :
    chainTranslation (-k) n = n - k := by
  rw [chainTranslation_apply]
  ring

theorem chainTranslation_apply_comp (k l n : Int) :
    chainTranslation k (chainTranslation l n) = n + (k + l) := by
  rw [chainTranslation_apply, chainTranslation_apply]
  ring

theorem chainTranslation_apply_add' (k l n : Int) :
    chainTranslation (k + l) n = n + k + l := by
  rw [chainTranslation_apply]
  ring

theorem graphAut_one' : FrobeniusPictureGraphAut (1 : Equiv.Perm Int) := graphAut_one

theorem graphAut_translation_apply (k : Int) (n : Int) :
    chainTranslation k n = n + k := chainTranslation_apply k n

end LeanFormal.IUT
