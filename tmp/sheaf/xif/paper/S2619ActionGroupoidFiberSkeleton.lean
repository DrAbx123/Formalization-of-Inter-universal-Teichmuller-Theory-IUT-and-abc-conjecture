import Mathlib.CategoryTheory.Action
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import tmp.sheaf.xif.paper.S2618LocalModelActual
import Iut.Foundations.Orbicurve

noncomputable section
open CategoryTheory
open Iut
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton

universe u
variable (l : PrimeGeFive) (F : Type u) [CommRing F]

abbrev S2619G : Type := ZMod l.value

structure S2619ActionGroupoidData where
  U : Iut.SchemeOverField F
  rho : S2619G l →* CategoryTheory.Aut U

variable (D : S2619ActionGroupoidData (l := l) (F := F))

abbrev S2619Hom (V : (Iut.SchemeOverField F)ᵒᵖ) : Type u :=
  V.unop ⟶ D.U

instance S2619MulAction (V : (Iut.SchemeOverField F)ᵒᵖ) :
    MulAction (S2619G l) (S2619Hom (l := l) (F := F) D V) where
  smul g f := f ≫ ((D.rho g).hom : D.U ⟶ D.U)
  one_smul f := by
    change f ≫ ((D.rho 1).hom : D.U ⟶ D.U) = f
    rw [map_one]
    change f ≫ (𝟙 D.U) = f
    simp
  mul_smul g h f := by
    change f ≫ ((D.rho (g * h)).hom : D.U ⟶ D.U) =
      (f ≫ ((D.rho h).hom : D.U ⟶ D.U)) ≫ ((D.rho g).hom : D.U ⟶ D.U)
    rw [map_mul]
    change f ≫ ((D.rho h).hom ≫ (D.rho g).hom) =
      (f ≫ (D.rho h).hom) ≫ (D.rho g).hom
    rw [Category.assoc]

noncomputable def S2619FiberAt (V : (Iut.SchemeOverField F)ᵒᵖ) : Cat.{0, u} :=
  Cat.of (CategoryTheory.ActionCategory (S2619G l) (S2619Hom (l := l) (F := F) D V))

noncomputable def S2619PullFunctor
    {V V' : (Iut.SchemeOverField F)ᵒᵖ}
    (h : V ⟶ V') :
    S2619FiberAt (l := l) (F := F) D V ⥤
      S2619FiberAt (l := l) (F := F) D V' where
  obj f := (⟨CategoryTheory.SingleObj.star (S2619G l), h.unop ≫ f.back⟩ :
    S2619FiberAt (l := l) (F := F) D V')
  map {f g} η := by
    rcases f with ⟨fst, fback⟩
    rcases g with ⟨gst, gback⟩
    cases fst
    cases gst
    refine Subtype.mk η.val ?_
    change (h.unop ≫ fback) ≫ ((D.rho (show S2619G l from η.val)).hom : D.U ⟶ D.U) =
      h.unop ≫ gback
    rw [Category.assoc]
    exact congrArg (fun z => h.unop ≫ z) η.property
  map_id f := Subtype.ext rfl
  map_comp {f g h} η θ := Subtype.ext rfl

structure S2619ActionGroupoidFiberCandidate where
  fiber : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0, u}
  fiber_obj_eq : ∀ V : (Iut.SchemeOverField F)ᵒᵖ,
    fiber.obj (LocallyDiscrete.mk V) = S2619FiberAt (l := l) (F := F) D V

variable (fib : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0, u})

def S2619PrestackGoal : Prop :=
  fib.IsPrestack (Iut.SchemeOverField.etaleTopology F)

def S2619PresheafHomSheafGoal
    {S : Iut.SchemeOverField F}
    (M N : fib.obj (LocallyDiscrete.mk (Opposite.op S))) : Prop :=
  Presheaf.IsSheaf
    ((Iut.SchemeOverField.etaleTopology F).over S)
    (fib.presheafHom M N)

#check S2619PullFunctor
#check S2619FiberAt
#check S2619PresheafHomSheafGoal

end LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
end
