import Mathlib.CategoryTheory.Galois.Basic

noncomputable section
open CategoryTheory CategoryTheory.Limits

universe u v

section

variable {C : Type u} [Category.{v, u} C]

example (G : Type) [Group G] (A : C) :
    HasColimit ((Functor.const (SingleObj G)).obj A) := by
  let c : Cocone ((Functor.const (SingleObj G)).obj A) :=
    { pt := A
      ι := 𝟙 _ }
  refine ⟨c, ?_⟩
  refine
    { desc := fun s => s.ι.app (SingleObj.star G)
      fac := ?_
      uniq := ?_ }
  · intro s j
    have hj : j = SingleObj.star G := Quiver.SingleObj.ext
    subst hj
    exact Category.id_comp _
  · intro s m hm
    exact (Category.id_comp m).symm.trans (hm (SingleObj.star G))

example {X Y : C} (hX : IsInitial X) (i : X ⟶ Y) [Mono i] :
    ∃ (Z : C) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u)) := by
  refine ⟨Y, 𝟙 Y, ⟨?_⟩⟩
  refine BinaryCofan.IsColimit.mk (s := BinaryCofan.mk i (𝟙 Y))
    (fun {T} f g => g) ?_ ?_ ?_
  · intro T f g
    rw [BinaryCofan.mk_inl]
    exact IsInitial.hom_ext hX (i ≫ g) f
  · intro T f g
    rw [BinaryCofan.mk_inr]
    exact Category.id_comp g
  · intro T f g m hm1 hm2
    rw [BinaryCofan.mk_inr] at hm2
    have hm2' : (𝟙 Y) ≫ (show Y ⟶ T from m) = g := hm2
    change (show Y ⟶ T from m) = g
    simpa using hm2'

end
