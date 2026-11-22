import Iut.Foundations.Orbicurve
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 400000

namespace LeanFormal.IUT.XiFPaper.S1898Mini

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT

variable (F : Type) [Field F]
variable (X : Iut.SchemeOverField F)
variable (g : X ⟶ X)

abbrev Stack (F : Type) [Field F] (X : Iut.SchemeOverField F) :
    Iut.EtaleStackPseudofunctor F :=
  Iut.schemeRepresentableEtalePseudofunctor F X

noncomputable def app
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) :
    (Stack F X).obj U ⟶ (Stack F X).obj U :=
  (Discrete.functor (fun P : Opposite.unop U.as ⟶ X =>
    Discrete.mk (P ≫ g))).toCatHom

instance subhom {C : Cat.{0, 0}} {A : Type}
    (G H : C ⟶ Cat.of (Discrete A)) : Subsingleton (G ⟶ H) := by
  constructor
  intro x y
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext Z
  apply ULift.ext
  exact Subsingleton.elim _ _

noncomputable def hom : Pseudofunctor.StrongTrans (Stack F X) (Stack F X) where
  app U := app F X g U
  naturality {a b} f := by
    refine Cat.Hom.isoMk (eqToIso ?_)
    apply CategoryTheory.Functor.ext
    · intro P Q h
      apply ULift.ext
      exact Subsingleton.elim _ _
    · intro P
      obtain ⟨g'⟩ := f
      apply Discrete.ext
      change g'.unop ≫ P.as ≫ g = g'.unop ≫ P.as ≫ g
      rfl
  naturality_naturality := by
    intro a b f h eta
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext Z
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_id := by
    intro a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext Z
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_comp := by
    intro a b c f h
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext Z
    apply ULift.ext
    exact Subsingleton.elim _ _

theorem hom_ne_id (h : g ≠ 𝟙 X) :
    hom F X g ≠ Pseudofunctor.StrongTrans.id (Stack F X) := by
  intro heq
  have h1 := congrArg (fun e : Pseudofunctor.StrongTrans (Stack F X) (Stack F X) =>
    (e.app (LocallyDiscrete.mk (Opposite.op X))).toFunctor.obj
      (Discrete.mk (𝟙 X))) heq
  have h2 : Discrete.mk g = Discrete.mk (𝟙 X) := by
    simpa [hom, app, Stack, Pseudofunctor.StrongTrans.id] using h1
  exact h (congrArg Discrete.as h2)

noncomputable def hom_comp_hom_iso (hgg : g ≫ g = 𝟙 X) :
    Pseudofunctor.StrongTrans.vcomp (hom F X g) (hom F X g) ≅
      Pseudofunctor.StrongTrans.id (Stack F X) := by
  refine Pseudofunctor.StrongTrans.isoMk (fun U => ?_) ?_
  · apply Cat.Hom.isoMk
    apply eqToIso
    apply CategoryTheory.Functor.ext
    · intro P Q h
      apply ULift.ext
      exact Subsingleton.elim _ _
    · intro P
      apply Discrete.ext
      change P.as ≫ g ≫ g = P.as
      rw [hgg, Category.comp_id]
  · intro a b f
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext Z
    apply ULift.ext
    exact Subsingleton.elim _ _

#check hom F X g
#check hom_ne_id F X g
#check hom_comp_hom_iso F X g

end LeanFormal.IUT.XiFPaper.S1898Mini