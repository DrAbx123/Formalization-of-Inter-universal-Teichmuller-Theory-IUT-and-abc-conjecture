import tmp.sheaf.xif.paper.S2495cFUnconditionalActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2510RestrictScalarsActual

variable (F : Type u) [Field F]

theorem S2510SchemeRestrict_self :
    schemeRestrictScalars F F = 𝟭 (Iut.SchemeOverField F) := by
  simp [schemeRestrictScalars, Over.mapId_eq]

end LeanFormal.IUT.XiFPaper.S2510RestrictScalarsActual
end