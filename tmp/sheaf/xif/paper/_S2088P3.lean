import tmp.sheaf.xif.paper.S2070CurveEtaleFundamentalCardActual
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open LeanFormal.IUT.Foundations.Geometry
universe u

#check @TypeCat.ofHom_apply
#check @TypeCat.comp_apply
#check @TypeCat.id_apply
#check @CategoryTheory.ConcreteCategory.id_apply
#check @CategoryTheory.ConcreteCategory.comp_apply
#check @CategoryTheory.ConcreteCategory.congr_hom

example {α β : Type u} (f : α ⟶ β) (a : α) : f a = (f : α → β) a := rfl
example {α β : Type u} (g : α → β) (a : α) : (TypeCat.ofHom g) a = g a := rfl
example {α β γ : Type u} (f : α ⟶ β) (g : β ⟶ γ) (a : α) : (f ≫ g) a = g (f a) := rfl

example {X : Scheme.{u}} {Om : Type u} [Field Om] {x : Spec (CommRingCat.of Om) ⟶ X}
    {Y Z : FiniteEtaleCover X} (f : Y ⟶ Z) (s : geometricFiberObject Om x Y) :
    (geometricFiberFunctor Om x).map f s = geometricFiberMap f s := rfl

example {X : Scheme.{u}} {Om : Type u} [Field Om] {x : Spec (CommRingCat.of Om) ⟶ X}
    {Y Z : FiniteEtaleCover X} (f : Y ⟶ Z) (s : geometricFiberObject Om x Y) :
    (geometricFiberMap f s).1 = s.1 ≫ Over.Hom.left f.1 := rfl

example {S : Scheme.{u}} (Om : Type u) [Field Om] (x : Spec (CommRingCat.of Om) ⟶ S) :
    geometricFiberObject Om x (terminalCover S)
      = {s : Spec (CommRingCat.of Om) ⟶ S // s ≫ 𝟙 S = x} := rfl

-- IsTerminal of a subsingleton-inhabited type in Type
example : IsTerminal (PUnit : Type) := by
  apply IsTerminal.ofUnique
  intro Y
  exact ⟨⟨fun _ => PUnit.unit⟩, fun a b => by ext y; simp⟩

end
