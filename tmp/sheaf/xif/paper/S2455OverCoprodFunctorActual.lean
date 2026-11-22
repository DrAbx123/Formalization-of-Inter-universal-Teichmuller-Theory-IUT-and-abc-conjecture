import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Comma.Over.Basic

noncomputable section
open CategoryTheory Opposite Limits
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2455OverCoprodFunctorActual

universe v u

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]

/-- Pullback of an object over X ⨿ Y to the two summands, as a functor
Over (X ⨿ Y) ⟶ Over X × Over Y. -/
noncomputable def S2455OverCoprodPullback (X Y : C) :
    Over (X ⨿ Y) ⟶ Over X × Over Y where
  obj Z := (Over.map (coprod.inl : X ⟶ X ⨿ Y) |>.obj Z,
    Over.map (coprod.inr : Y ⟶ X ⨿ Y) |>.obj Z)
  map f := (Over.map (coprod.inl : X ⟶ X ⨿ Y) |>.map f,
    Over.map (coprod.inr : Y ⟶ X ⨿ Y) |>.map f)
  map_id Z := by simp
  map_comp f g := by simp

#print axioms S2455OverCoprodPullback

end LeanFormal.IUT.XiFPaper.S2455OverCoprodFunctorActual

end
