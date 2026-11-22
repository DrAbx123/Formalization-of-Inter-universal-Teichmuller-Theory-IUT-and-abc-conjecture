import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Creates

noncomputable section
open CategoryTheory
open CategoryTheory.Limits

namespace ProbeS1914f

universe u v

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

example {X Y : P.FullSubcategory} (i : X ⟶ Y)
    {Z0 : C} (u0 : Z0 ⟶ Y.obj)
    (hc0 : IsColimit (BinaryCofan.mk i.hom u0))
    (P0 : P.FullSubcategory) (e : Z0 ≅ P0.obj) :
    ∃ (Z : P.FullSubcategory) (u : Z ⟶ Y),
      Nonempty (IsColimit (BinaryCofan.mk i u)) := by
  let c1 : Cocone (pair X P0 ⋙ P.ι) := BinaryCofan.mk i.hom (e.inv ≫ u0)
  have hc1 : IsColimit c1 :=
    BinaryCofan.isColimitCompRightIso (BinaryCofan.mk i.hom u0) e.inv hc0
  let u : P0 ⟶ Y := ObjectProperty.homMk (e.inv ≫ u0)
  letI : CreatesColimit (pair X P0) P.ι :=
    createsColimitFullSubcategoryInclusion' (pair X P0) hc1 (show P c1.pt from Y.property)
  have hLift : IsColimit (liftColimit hc1) := liftedColimitIsColimit hc1
  let cLift : BinaryCofan X P0 := liftColimit hc1
  have hcLift : IsColimit cLift := hLift
  have hleg1 : cLift.inl = i := by
    apply ObjectProperty.hom_ext
    rfl
  have hleg2 : cLift.inr = u := by
    apply ObjectProperty.hom_ext
    rfl
  refine ⟨P0, u, ⟨?_⟩⟩
  refine IsColimit.ofIsoColimit hcLift (BinaryCofan.ext (Iso.refl Y) ?_ ?_)
  · simpa [hleg1] using Category.comp_id (f := cLift.inl)
  · simpa [hleg2] using Category.comp_id (f := cLift.inr)

end ProbeS1914f
