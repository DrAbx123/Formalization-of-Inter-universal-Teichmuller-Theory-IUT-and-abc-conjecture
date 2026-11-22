/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FrobeniusPictureArrowFactsActual

/-! # Reuse: corollaries of the Gamma arrow facts -/

namespace LeanFormal.IUT

theorem frobeniusPictureArrow_four {a b c d e : Int}
    (h1 : FrobeniusPictureArrow a b) (h2 : FrobeniusPictureArrow b c)
    (h3 : FrobeniusPictureArrow c d) (h4 : FrobeniusPictureArrow d e) :
    e = a + 4 := by
  have hd : d = a + 3 := frobeniusPictureArrow_comp_three h1 h2 h3
  rw [FrobeniusPictureArrow] at h4
  omega

theorem frobeniusPictureArrow_comp_iff_three (a k : Int) :
    (Exists fun m1 => Exists fun m2 =>
      FrobeniusPictureArrow a m1 ∧ FrobeniusPictureArrow m1 m2 ∧
        FrobeniusPictureArrow m2 k) ↔ k = a + 3 := by
  constructor
  · rintro ⟨m1, m2, h1, h2, h3⟩
    exact frobeniusPictureArrow_comp_three h1 h2 h3
  · intro hk
    refine ⟨a + 1, a + 2, rfl, rfl, ?_⟩
    rw [FrobeniusPictureArrow]
    omega

theorem frobeniusPictureArrow_succ_succ (n : Int) :
    FrobeniusPictureArrow n (n + 1) ∧ FrobeniusPictureArrow (n + 1) (n + 2) := 
  ⟨rfl, rfl⟩

theorem frobeniusPictureArrow_iterate_succ (n : Int) (k : Nat) :
    FrobeniusPictureArrow (n + k) (n + k + 1) := rfl

end LeanFormal.IUT
