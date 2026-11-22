/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Prime-strips (F/D): category-skeleton laws -/

namespace LeanFormal.IUT.XiFPaper.PrimeStripCategorySkeletonActual

universe u

structure CatSkel where
  Obj : Type u
  Hom : Obj → Obj → Type u
  id : ∀ X : Obj, Hom X X
  comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f
  assoc : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h)

variable (C : CatSkel.{u})

def catOp : CatSkel.{u} where
  Obj := C.Obj
  Hom X Y := C.Hom Y X
  id X := C.id X
  comp f g := C.comp g f
  id_comp f := C.comp_id f
  comp_id f := C.id_comp f
  assoc f g h := (C.assoc h g f).symm

theorem catOp_obj : C.catOp.Obj = C.Obj := rfl

theorem catOp_op : C.catOp.catOp = C := by
  cases C
  rfl

theorem catOp_comp {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z) :
    C.catOp.comp (show C.catOp.Hom Z Y from g) (show C.catOp.Hom Y X from f) =
      (show C.catOp.Hom Z X from C.comp f g) := rfl

theorem id_comp_apply {X Y : C.Obj} (f : C.Hom X Y) : C.comp (C.id X) f = f :=
  C.id_comp f

theorem comp_id_apply {X Y : C.Obj} (f : C.Hom X Y) : C.comp f (C.id Y) = f :=
  C.comp_id f

theorem comp_assoc_apply {W X Y Z : C.Obj} (f : C.Hom W X) (g : C.Hom X Y)
    (h : C.Hom Y Z) : C.comp (C.comp f g) h = C.comp f (C.comp g h) :=
  C.assoc f g h

end LeanFormal.IUT.XiFPaper.PrimeStripCategorySkeletonActual
