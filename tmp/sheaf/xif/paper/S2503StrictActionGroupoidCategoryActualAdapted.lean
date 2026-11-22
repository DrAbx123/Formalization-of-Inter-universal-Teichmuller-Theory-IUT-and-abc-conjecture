import tmp.sheaf.xif.paper.S2501StrictifiedFiberActual
import tmp.sheaf.xif.paper.S2473ActionGroupoidFiberActual

noncomputable section
open CategoryTheory
universe v u

namespace LeanFormal.IUT.XiFPaper.S2503StrictActionGroupoidCategoryActualAdapted
open LeanFormal.IUT.XiFPaper.S2501StrictifiedFiberActual
open LeanFormal.IUT.XiFPaper.S2473ActionGroupoidFiberActual

variable (C : Type u) [Category.{v} C]

/-- The strict square iso used as the coherence of the action groupoid. -/
noncomputable def S2503Sq :
    S2501Sigma C ⋙ S2501Sigma C ≅ 𝟭 (S2501StrictFiber C) :=
  eqToIso (S2501Sigma_sq C)

local notation "C'" => S2501StrictFiber C

instance S2503Category : Category C' where
  Hom x y := S2473Hom (S2501Sigma C) x y
  id x := S2473Id (S2501Sigma C) x
  comp f g := S2473Comp (S2501Sigma C) (S2503Sq C) f g
  id_comp := by
    intro x y f
    rcases f with f | f <;> simp [S2473Id, S2473Comp]
  comp_id := by
    intro x y f
    rcases f with f | f <;> simp [S2473Id, S2473Comp]
  assoc := by
    intro w x y z f g h
    have hnat : ∀ {a b : C'} (k : a ⟶ b),
        (S2503Sq C).hom.app a ≫ k =
          (S2501Sigma C ⋙ S2501Sigma C).map k ≫ (S2503Sq C).hom.app b := by
      intro a b k
      simpa [Functor.comp_map, Functor.id_map] using
        (S2503Sq C).hom.naturality k |>.symm
    have hm : ∀ z,
        (S2501Sigma C).map ((S2503Sq C).hom.app z) =
          (S2503Sq C).hom.app ((S2501Sigma C).obj z) := by
      intro z
      dsimp [S2503Sq, eqToIso]
      simp only [eqToHom_app]
      change (S2501Sigma C).map
          (eqToHom (Functor.congr_obj (S2501Sigma_sq C) z)) =
        eqToHom (Functor.congr_obj (S2501Sigma_sq C) ((S2501Sigma C).obj z))
      rw [eqToHom_map]
      congr 1
    rcases f with f | f <;> rcases g with g | g <;> rcases h with h | h <;>
      dsimp [S2473Comp]
    all_goals
      first
      | cat_disch
      | apply congrArg Sum.inl
        dsimp [S2473Comp, S2501Sigma] at *
        simp only [Prod.prod_comp]
        have h1 : (S2503Sq C).hom.app y ≫ h =
            (S2501Sigma C ⋙ S2501Sigma C).map h ≫ (S2503Sq C).hom.app z := hnat h
        have h1fst := congrArg (fun f => f.1) h1
        have h1snd := congrArg (fun f => f.2) h1
        apply Prod.ext
        · rw [show ((S2503Sq C).hom.app y).1 ≫ h.1 =
              (((S2503Sq C).hom.app y) ≫ h).1 from (prod_comp_fst).symm]
          rw [h1fst]
          simp [Functor.map_comp, Category.assoc]
        · rw [show ((S2503Sq C).hom.app y).2 ≫ h.2 =
              (((S2503Sq C).hom.app y) ≫ h).2 from (prod_comp_snd).symm]
          rw [h1snd]
          simp [Functor.map_comp, Category.assoc]
      | apply congrArg Sum.inr
        let h' : (𝟭 C').obj y ⟶ (S2501Sigma C).obj z := h
        have h1 :
            (show (S2501Sigma C).obj ((S2501Sigma C).obj y) ⟶ (𝟭 C').obj y from
              (S2503Sq C).hom.app y) ≫ h' =
            (S2501Sigma C ⋙ S2501Sigma C).map h' ≫
              (S2503Sq C).hom.app ((S2501Sigma C).obj z) := hnat h'
        change
          (f ≫ (S2501Sigma C).map g ≫
            (show (S2501Sigma C).obj ((S2501Sigma C).obj y) ⟶ (𝟭 C').obj y from
              (S2503Sq C).hom.app y)) ≫ h' =
          f ≫ (S2501Sigma C).map
            (g ≫ (S2501Sigma C).map h ≫ (S2503Sq C).hom.app z)
        simp only [Category.assoc]
        rw [h1]
        rw [← hm z]
        rfl

#check S2503Category

end LeanFormal.IUT.XiFPaper.S2503StrictActionGroupoidCategoryActualAdapted
end