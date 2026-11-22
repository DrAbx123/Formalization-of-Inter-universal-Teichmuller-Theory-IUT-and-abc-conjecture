import tmp.sheaf.xif.paper.S2473ActionGroupoidFiberActual

noncomputable section
open CategoryTheory
universe v u

namespace LeanFormal.IUT.XiFPaper.S2474ActionGroupoidCategoryActualAdapted
open LeanFormal.IUT.XiFPaper.S2473ActionGroupoidFiberActual

variable {C : Type u} [Category.{v} C]
variable (σ : C ⥤ C) (sq : σ ⋙ σ ≅ 𝟭 C)

instance S2474Category : Category C where
  Hom x y := S2473Hom σ x y
  id x := S2473Id σ x
  comp {x y z} f g := S2473Comp σ sq f g
  id_comp := by
    intro x y f
    rcases f with f | f <;> simp [S2473Id, S2473Comp, Functor.map_id]
  comp_id := by
    intro x y f
    rcases f with f | f <;> simp [S2473Id, S2473Comp]
  assoc := by
    intro w x y z f g h
    rcases f with f | f <;> rcases g with g | g <;> rcases h with h | h <;>
      simp [S2473Comp, Category.assoc, Functor.map_comp, sq.hom.naturality]

#check S2474Category

end LeanFormal.IUT.XiFPaper.S2474ActionGroupoidCategoryActualAdapted
end
