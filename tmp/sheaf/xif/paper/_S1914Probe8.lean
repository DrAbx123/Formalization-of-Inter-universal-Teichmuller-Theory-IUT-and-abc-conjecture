import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

noncomputable section
open CategoryTheory
open CategoryTheory.Limits

namespace ProbeS1914h

universe u v

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

example {X Y : P.FullSubcategory} (i : X ⟶ Y)
    {Z0 : C} (u0 : Z0 ⟶ Y.obj)
    (hc0 : IsColimit (BinaryCofan.mk i.hom u0))
    (P0 : P.FullSubcategory) (e : Z0 ≅ P0.obj) :
    ∃ (Z : P.FullSubcategory) (u : Z ⟶ Y),
      Nonempty (IsColimit (BinaryCofan.mk i u)) := by
  have hc1 : IsColimit (BinaryCofan.mk i.hom (e.inv ≫ u0)) :=
    BinaryCofan.isColimitCompRightIso (BinaryCofan.mk i.hom u0) e.inv hc0
  let u : P0 ⟶ Y := ObjectProperty.homMk (e.inv ≫ u0)
  refine ⟨P0, u, ⟨?_⟩⟩
  refine BinaryCofan.IsColimit.mk (BinaryCofan.mk i u)
    (fun {T} f g => ObjectProperty.homMk (BinaryCofan.IsColimit.desc hc1 f.hom g.hom)) ?_ ?_ ?_
  · intro T f g
    apply ObjectProperty.hom_ext
    change i.hom ≫ BinaryCofan.IsColimit.desc hc1 f.hom g.hom = f.hom
    exact BinaryCofan.IsColimit.inl_desc hc1 f.hom g.hom
  · intro T f g
    apply ObjectProperty.hom_ext
    change (e.inv ≫ u0) ≫ BinaryCofan.IsColimit.desc hc1 f.hom g.hom = g.hom
    exact BinaryCofan.IsColimit.inr_desc hc1 f.hom g.hom
  · intro T f g m hm1 hm2
    apply ObjectProperty.hom_ext
    change m.hom = BinaryCofan.IsColimit.desc hc1 f.hom g.hom
    apply BinaryCofan.IsColimit.hom_ext hc1
    · change i.hom ≫ m.hom = i.hom ≫ BinaryCofan.IsColimit.desc hc1 f.hom g.hom
      have hm1' : i.hom ≫ m.hom = f.hom :=
        congrArg (fun k : X ⟶ T => k.hom) hm1
      rw [hm1']
      exact (BinaryCofan.IsColimit.inl_desc hc1 f.hom g.hom).symm
    · change (e.inv ≫ u0) ≫ m.hom =
        (e.inv ≫ u0) ≫ BinaryCofan.IsColimit.desc hc1 f.hom g.hom
      have hm2' : (e.inv ≫ u0) ≫ m.hom = g.hom :=
        congrArg (fun k : P0 ⟶ T => k.hom) hm2
      rw [hm2']
      exact (BinaryCofan.IsColimit.inr_desc hc1 f.hom g.hom).symm

end ProbeS1914h
