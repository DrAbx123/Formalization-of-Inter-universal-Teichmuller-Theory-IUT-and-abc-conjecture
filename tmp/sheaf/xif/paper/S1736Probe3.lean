import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.EssentialImage

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1736Probe3

open CategoryTheory
open CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper

abbrev Cover : Type 1 := S1728Cover
abbrev CoverMap (A B : Cover) : Type 1 := S1728CoverMap A B

variable (H : (A B : Cover) → Type)
variable (e : ∀ A B, H A B ≃ CoverMap A B)

abbrev SmallCat : Category.{0,1} Cover := S1728CategoryOfHomEquiv Cover H e

local instance smallCatInst : Category.{0,1} Cover := SmallCat H e

noncomputable def smallToActual : @CategoryTheory.Functor Cover (SmallCat H e) Cover S1728ActualCategory11 :=
  @CategoryTheory.Functor.mk Cover (SmallCat H e) Cover S1728ActualCategory11
    (fun X => X)
    (fun {X Y} f => e X Y f)
    (by intro X; show e X X ((e X X).symm (𝟙 X)) = 𝟙 X; simp)
    (by intro X Y Z f g; show e X Z ((e X Z).symm (e X Y f ≫ e Y Z g)) = e X Y f ≫ e Y Z g; simp)

#check smallToActual H e
#check (smallToActual H e).Full

instance : (smallToActual H e).Full where
  map_surjective {X Y} f := ⟨(e X Y).symm f, by
    show e X Y ((e X Y).symm f) = f
    simp⟩

end LeanFormal.IUT.XiFPaper.S1736Probe3
