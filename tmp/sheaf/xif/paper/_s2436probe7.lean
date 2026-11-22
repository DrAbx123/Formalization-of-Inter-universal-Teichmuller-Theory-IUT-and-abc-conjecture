import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.ZMod.Basic

open CategoryTheory
open scoped Bicategory

set_option autoImplicit false

namespace Probe2436

abbrev T : AddCommGrpCat.{0} := AddCommGrpCat.of (ZMod 2)
abbrev X : AddCommGrpCat.{0} := AddCommGrpCat.of ℤ

noncomputable def m : X ⟶ T := AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2))

noncomputable def yonedaCat : (AddCommGrpCat.{0})ᵒᵖ ⥤ Cat.{0,0} where
  obj U := Cat.of (Discrete (U.unop ⟶ T))
  map {U V} g := (Discrete.functor (fun h : U.unop ⟶ T => Discrete.mk (g.unop ≫ h))).toCatHom
  map_id U := by
    apply Cat.Hom.ext
    apply Discrete.functor_ext
    intro i
    rfl
  map_comp {U V W} f g := by
    apply Cat.Hom.ext
    apply Discrete.functor_ext
    intro i
    simp [Category.assoc]

noncomputable def F : Pseudofunctor (LocallyDiscrete (AddCommGrpCat.{0})ᵒᵖ) Cat.{0,0} :=
  yonedaCat.toPseudofunctor'

variable {Y : AddCommGrpCat.{0}} (g : Y ⟶ X)

example : (F.map g.op.toLoc).toFunctor.obj (Discrete.mk m) = Discrete.mk (g ≫ m) := rfl

example : ((F.map g.op.toLoc).toFunctor.obj (Discrete.mk m) : Discrete (Y ⟶ T)) ⟶
    (F.map g.op.toLoc).toFunctor.obj (Discrete.mk m) := 𝟙 _

example (h : (F.map g.op.toLoc).toFunctor.obj (Discrete.mk m) =
    (F.map g.op.toLoc).toFunctor.obj (Discrete.mk m)) : True := by
  haveI : Subsingleton ((F.map g.op.toLoc).toFunctor.obj (Discrete.mk m) ⟶
      (F.map g.op.toLoc).toFunctor.obj (Discrete.mk m)) :=
    Discrete.instSubsingletonDiscreteHom _ _
  trivial

end Probe2436
