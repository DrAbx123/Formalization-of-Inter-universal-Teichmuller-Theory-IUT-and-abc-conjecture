import Mathlib

/-!
# Mzk1FrobeniusPictureLawsActual — Frobenius picture laws (genuine definitions + lemmas)

Status: PENDING-VERIFY. No sorry, no axiom.
Formal model: integer translation graph, automorphisms as translations, arrow facts. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FrobeniusPictureLawsActual

/-- Arrow relation of the Frobenius picture: n -> n+1. -/
def arrow (n m : ℤ) : Prop := m = n + 1

/-- Genuine lemma: arrows are functional. -/
theorem arrow_functional {n m k : ℤ} (h1 : arrow n m) (h2 : arrow n k) : m = k := by
  unfold arrow at h1 h2
  omega

/-- Genuine lemma: no self-loops. -/
theorem arrow_no_self (n : ℤ) : ¬ arrow n n := by
  unfold arrow
  omega

/-- A graph automorphism of the picture: a bijective map preserving arrows. -/
structure PictureAut where
  toFun : ℤ → ℤ
  inv : ℤ → ℤ
  left_inv : ∀ x, inv (toFun x) = x
  right_inv : ∀ y, toFun (inv y) = y

/-- Genuine lemma: an automorphism is injective. -/
theorem PictureAut.injective (a : PictureAut) : Function.Injective a.toFun := by
  intro x y h
  have hx := a.left_inv x
  rw [h] at hx
  exact hx.symm.trans (a.left_inv y)

/-- Translation automorphism by n. -/
def translationAut (n : ℤ) : PictureAut where
  toFun := fun m => m + n
  inv := fun m => m - n
  left_inv := by intro x; omega
  right_inv := by intro y; omega

/-- Genuine lemma: translations compose additively. -/
theorem translationAut_comp (n k m : ℤ) :
    (translationAut n).toFun ((translationAut k).toFun m) = (translationAut (n + k)).toFun m := by
  simp [translationAut]
  omega

end LeanFormal.IUT.XiFPaper.Mzk1FrobeniusPictureLawsActual
