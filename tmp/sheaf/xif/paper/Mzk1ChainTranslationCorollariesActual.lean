/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ChainTranslationLawActual

/-! # Reuse: corollaries of the translation group law -/

namespace LeanFormal.IUT

theorem chainTranslation_add_add (k l m : Int) :
    chainTranslation ((k + l) + m) =
      chainTranslation k * chainTranslation l * chainTranslation m := by
  rw [chainTranslation_add, chainTranslation_add, mul_assoc]

theorem chainTranslation_add_apply₂ (k l m n : Int) :
    chainTranslation ((k + l) + m) n =
      chainTranslation k (chainTranslation l (chainTranslation m n)) := by
  rw [chainTranslation_add_apply, chainTranslation_add_apply, chainTranslation_add_apply]

theorem chainTranslation_neg_add (k : Int) :
    chainTranslation k * chainTranslation (-k) = (1 : Equiv.Perm Int) := by
  rw [← chainTranslation_add]
  simp [chainTranslation_zero_eq_one]

theorem chainTranslation_neg_add_left (k : Int) :
    chainTranslation (-k) * chainTranslation k = (1 : Equiv.Perm Int) := by
  rw [← chainTranslation_add]
  simp [chainTranslation_zero_eq_one]

theorem chainTranslation_add_comm (k l : Int) :
    chainTranslation (k + l) = chainTranslation (l + k) := by
  rw [chainTranslation_add, chainTranslation_add, mul_comm]

theorem chainTranslation_add_apply_comm (k l n : Int) :
    chainTranslation (k + l) n = chainTranslation (l + k) n := by
  rw [chainTranslation_add_comm]

end LeanFormal.IUT
