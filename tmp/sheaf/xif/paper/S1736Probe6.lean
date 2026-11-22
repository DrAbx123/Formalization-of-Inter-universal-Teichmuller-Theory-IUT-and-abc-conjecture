import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import Mathlib.CategoryTheory.Galois.Basic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1736Probe6
open CategoryTheory
open CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper

abbrev Cover : Type 1 := S1728Cover
abbrev CoverMap (A B : Cover) : Type 1 := S1728CoverMap A B

section Target
variable (H : (A B : Cover) → Type)
variable (e : ∀ A B, H A B ≃ CoverMap A B)

abbrev SmallCat : Category.{0,1} Cover := S1728ActualCategory01 H e

variable [C : Category.{0,1} Cover]

def GaloisCategoryOfInputs
    (P : @PreGaloisCategory.{1,0} Cover C)
    (F : Cover ⥤ FintypeCat.{0})
    (hF : @PreGaloisCategory.FiberFunctor Cover C P F) :
    @GaloisCategory.{1,0} Cover C :=
  { toPreGaloisCategory := P
    hasFiberFunctor := ⟨F, ⟨hF⟩⟩ }

end Target

end LeanFormal.IUT.XiFPaper.S1736Probe6
