import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence
import Mathlib.CategoryTheory.Adjunction.Limits

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1736Probe

open CategoryTheory
open CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual

universe u

variable {F : Type u} [Field F] {X : HyperbolicOrbicurve F}

#check S1728CoverCategory11 (F := F) (X := X)
#check @PreGaloisCategory.{u+1, u+1} (OrbicurveFiniteEtaleCover X) (S1728CoverCategory11 (F := F) (X := X))

end LeanFormal.IUT.XiFPaper.S1736Probe
