import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

noncomputable section
open CategoryTheory
open CategoryTheory.Limits

namespace ProbeS1914g

universe u v

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

example {X Y : P.FullSubcategory} (i : X ⟶ Y)
    {Z0 : C} (u0 : Z0 ⟶ Y.obj)
    (hc0 : IsColimit (BinaryCofan.mk i.hom u0))
    (P0 : P.FullSubcategory) (e : Z0 ≅ P0.obj) :
    True := by
  have hc1 : IsColimit (BinaryCofan.mk i.hom (e.inv ≫ u0)) :=
    BinaryCofan.isColimitCompRightIso (BinaryCofan.mk i.hom u0) e.inv hc0
  let u : P0 ⟶ Y := ObjectProperty.homMk (e.inv ≫ u0)
  let desc : ∀ {T : P.FullSubcategory}, (X ⟶ T) → (P0 ⟶ T) → (Y ⟶ T) :=
    fun {T} f g => ObjectProperty.homMk (BinaryCofan.IsColimit.desc hc1 f.hom g.hom)
  have fac1 : ∀ {T : P.FullSubcategory} (f : X ⟶ T) (g : P0 ⟶ T),
      (BinaryCofan.mk i u).inl ≫ desc f g = f := by
    intro T f g
    apply ObjectProperty.hom_ext
    trace_state
    sorry
  trivial

end ProbeS1914g
