/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.HodgeTheater.SourceThetaLinkGraphAutomorphismReduction

/-! # Frobenius-picture arrow relation: elementary facts -/

namespace LeanFormal.IUT

theorem frobeniusPictureArrow_iff (n m : Int) :
    FrobeniusPictureArrow n m ↔ m = n + 1 := Iff.rfl

theorem frobeniusPictureArrow_ne_self (n : Int) :
    ¬ FrobeniusPictureArrow n n := by
  simp [FrobeniusPictureArrow]

theorem frobeniusPictureArrow_unique (n m1 m2 : Int)
    (h1 : FrobeniusPictureArrow n m1) (h2 : FrobeniusPictureArrow n m2) :
    m1 = m2 := by
  rw [FrobeniusPictureArrow] at h1 h2
  omega

theorem frobeniusPictureArrow_succ (n : Int) :
    FrobeniusPictureArrow n (n + 1) := rfl

theorem frobeniusPictureArrow_target (n m : Int)
    (h : FrobeniusPictureArrow n m) : m = n + 1 := h

theorem frobeniusPictureArrow_comp {n m k : Int}
    (h1 : FrobeniusPictureArrow n m) (h2 : FrobeniusPictureArrow m k) :
    k = n + 2 := by
  rw [FrobeniusPictureArrow] at h1 h2
  omega

theorem frobeniusPictureArrow_comp_iff (n k : Int) :
    (Exists fun m => FrobeniusPictureArrow n m ∧ FrobeniusPictureArrow m k) ↔
      k = n + 2 := by
  constructor
  · rintro ⟨m, h1, h2⟩
    exact frobeniusPictureArrow_comp h1 h2
  · intro hk
    refine Exists.intro (n + 1) ⟨rfl, ?_⟩
    rw [FrobeniusPictureArrow]
    omega

theorem frobeniusPictureArrow_comp_three {a b c d : Int}
    (h1 : FrobeniusPictureArrow a b) (h2 : FrobeniusPictureArrow b c)
    (h3 : FrobeniusPictureArrow c d) : d = a + 3 := by
  rw [FrobeniusPictureArrow] at h1 h2 h3
  omega

end LeanFormal.IUT
-- force-fresh-recompile
