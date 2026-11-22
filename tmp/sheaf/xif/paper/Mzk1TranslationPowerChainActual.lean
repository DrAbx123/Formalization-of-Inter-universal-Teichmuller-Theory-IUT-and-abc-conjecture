/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FrobeniusGraphAutClosureActual
import tmp.sheaf.xif.paper.Mzk1ChainTranslationLawActual
import tmp.sheaf.xif.paper.Mzk1GraphAutTranslationUnicityActual

/-! # Chain: powers of Frobenius-picture automorphisms act as translations -/

namespace LeanFormal.IUT

theorem chainTranslation_pow (k : Int) (n : Nat) :
    (chainTranslation k) ^ n = chainTranslation (k * (n : Int)) := by
  induction n with
  | zero =>
      rw [Int.mul_zero, chainTranslation_zero_eq_one]
      simp
  | succ m ih =>
      rw [pow_succ, ih]
      rw [← chainTranslation_add]
      have h : k * (m : Int) + k = k * ((m + 1 : Nat) : Int) := by
        push_cast
        ring
      rw [h]

theorem frobeniusGraphAut_pow_arrow {sigma : Equiv.Perm Int}
    (h : FrobeniusPictureGraphAut sigma) (n : Nat) {a b : Int}
    (hab : FrobeniusPictureArrow a b) :
    FrobeniusPictureArrow (sigma ^ n a) (sigma ^ n b) := by
  have hp := FrobeniusPictureGraphAut_pow h n
  exact (hp a b).mp hab

theorem frobeniusGraphAut_pow_eq_translation {sigma : Equiv.Perm Int}
    (h : FrobeniusPictureGraphAut sigma) (n : Nat) :
    ∃ k : Int, sigma ^ n = chainTranslation (k * (n : Int)) := by
  obtain ⟨k, hk⟩ := graphAut_translation_param sigma h
  subst hk
  exact ⟨k, chainTranslation_pow k n⟩

end LeanFormal.IUT
