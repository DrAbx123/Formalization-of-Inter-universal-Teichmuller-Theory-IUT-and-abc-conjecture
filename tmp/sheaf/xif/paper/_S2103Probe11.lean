import Mathlib.CategoryTheory.Sites.SheafHom

noncomputable section
open CategoryTheory Opposite

namespace Probe

example {X Y Z : Type} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (ConcreteCategory.hom (f ≫ g)).toFun x = (ConcreteCategory.hom g).toFun ((ConcreteCategory.hom f).toFun x) := by
  rfl

example {X Y Z : Type} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) := by
  simp

example {X Y : Type} (f : X → Y) (x : X) : (↾f : X ⟶ Y) x = f x := by
  simp

end Probe
