import tmp.sheaf.xif.paper.S2619ActionGroupoidFiberSkeleton
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
open CategoryTheory
open Iut
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2667FiberCoherenceActual

universe u
variable (l : LeanFormal.IUT.PrimeGeFive) (F : Type u) [CommRing F]
variable (D : LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton.S2619ActionGroupoidData l F)

open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton

abbrev S2667FiberCat (V : (Iut.SchemeOverField F)ᵒᵖ) : Type u :=
  ActionCategory (S2619G l) (S2619Hom l F D V)

def S2667Pull {V V' : (Iut.SchemeOverField F)ᵒᵖ} (h : V ⟶ V') :
    S2667FiberCat l F D V ⥤ S2667FiberCat l F D V' :=
  S2619PullFunctor l F D h

lemma eqToHom_val {V : (Iut.SchemeOverField F)ᵒᵖ} {p q : S2667FiberCat l F D V}
    (h : p = q) :
    (eqToHom h).val = (1 : S2619G l) := by
  cases h
  rfl

lemma S2667Pull_obj_id (V : (Iut.SchemeOverField F)ᵒᵖ) (X : S2667FiberCat l F D V) :
    (S2667Pull l F D (𝟙 V)).obj X = X := by
  rcases X with ⟨c, a⟩
  cases c
  refine Sigma.ext ?_ ?_
  · exact Subsingleton.elim _ _
  · exact heq_of_eq (by simp [S2667Pull, S2619PullFunctor])

lemma S2667Pull_map_id (V : (Iut.SchemeOverField F)ᵒᵖ) (X Y : S2667FiberCat l F D V)
    (f : X ⟶ Y) :
    (S2667Pull l F D (𝟙 V)).map f =
      eqToHom (S2667Pull_obj_id l F D V X) ≫ f ≫ eqToHom (S2667Pull_obj_id l F D V Y).symm := by
  rcases X with ⟨cx, ax⟩
  cases cx
  rcases Y with ⟨cy, ay⟩
  cases cy
  rcases f with ⟨m, hm⟩
  have hmG : S2619G l := m
  apply Subtype.ext
  rw [ActionCategory.comp_val, ActionCategory.comp_val, eqToHom_val, eqToHom_val]
  dsimp [S2667Pull]
  change hmG = (1 : S2619G l) * hmG * 1
  simp

lemma S2667Pull_obj_comp {V V' V'' : (Iut.SchemeOverField F)ᵒᵖ} (f : V ⟶ V') (g : V' ⟶ V'')
    (X : S2667FiberCat l F D V) :
    (S2667Pull l F D (f ≫ g)).obj X =
      (S2667Pull l F D f ⋙ S2667Pull l F D g).obj X := by
  rcases X with ⟨c, a⟩
  cases c
  refine Sigma.ext ?_ ?_
  · exact Subsingleton.elim _ _
  · change HEq ((f ≫ g).unop ≫ a) (g.unop ≫ f.unop ≫ a)
    exact heq_of_eq (Category.assoc g.unop f.unop a)

lemma S2667Pull_map_comp {V V' V'' : (Iut.SchemeOverField F)ᵒᵖ} (f : V ⟶ V') (g : V' ⟶ V'')
    (X Y : S2667FiberCat l F D V) (h : X ⟶ Y) :
    (S2667Pull l F D (f ≫ g)).map h =
      eqToHom (S2667Pull_obj_comp l F D f g X) ≫
        (S2667Pull l F D f ⋙ S2667Pull l F D g).map h ≫
          eqToHom (S2667Pull_obj_comp l F D f g Y).symm := by
  rcases X with ⟨cx, ax⟩
  cases cx
  rcases Y with ⟨cy, ay⟩
  cases cy
  rcases h with ⟨m, hm⟩
  apply Subtype.ext
  dsimp only [S2667Pull, S2619PullFunctor, Functor.comp_obj, Functor.comp_map]
  rw [ActionCategory.comp_val, ActionCategory.comp_val, eqToHom_val, eqToHom_val]
  change (m : S2619G l) = 1 * (m : S2619G l) * 1
  simp

end LeanFormal.IUT.XiFPaper.S2667FiberCoherenceActual