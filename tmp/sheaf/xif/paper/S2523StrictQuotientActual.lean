import tmp.sheaf.xif.paper.S2503StrictActionGroupoidCategoryActual

noncomputable section
open CategoryTheory
universe v u

namespace LeanFormal.IUT.XiFPaper.S2523StrictQuotientActual
open LeanFormal.IUT.XiFPaper.S2501StrictifiedFiberActual
open LeanFormal.IUT.XiFPaper.S2473ActionGroupoidFiberActual
open LeanFormal.IUT.XiFPaper.S2503StrictActionGroupoidCategoryActual

variable (C : Type u) [Category.{v} C]

/-- The projection of the strictified sign action groupoid onto C, collapsing
the Bool factor and both branches. -/
noncomputable def S2523Pi : (S2501StrictFiber C) ⥤ C where
  obj p := p.1
  map {x y} f := Sum.elim (fun g : x ⟶ y => g.1) (fun g : x ⟶ (S2501Sigma C).obj y => g.1) f
  map_id x := by
    dsimp [S2473Id]; simp
  map_comp := by
    intro x y z f g
    rcases f with f | f <;> rcases g with g | g <;>
      simp [S2473Comp, S2501Sigma, S2501BoolSwap, Category.assoc]

#check S2523Pi
#print axioms S2523Pi
end LeanFormal.IUT.XiFPaper.S2523StrictQuotientActual
end