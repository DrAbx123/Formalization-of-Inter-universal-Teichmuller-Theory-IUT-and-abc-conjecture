import tmp.sheaf.xif.paper.S2049CurveEtaleCardActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveGaloisCategory

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2071CurveCardGaloisActual
open LeanFormal.IUT
open LeanFormal.IUT.Foundations.Geometry
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2049CurveEtaleCardActual
open CategoryTheory AlgebraicGeometry

universe u

/-- Actual finite etale cover category, aligned with S2049. -/
abbrev S2071CoverCategory (X : Scheme.{u}) : Type (u + 1) :=
  S2049CoverCategory X

/-- Exact missing completion from the actual pre-Galois structure (S2070) to
the card: quotient-by-finite-groups field, FintypeCat fiber with
FiberFunctor, profinite fundamental group, action, IsFundamentalGroup, and
geometric Pi/connectedness.  No inhabitant is asserted. -/
structure S2071CardGaloisCompletion (X : Scheme.{u}) where
  remaining : CurvePreGaloisCategoryRemainingFields X
  [preGaloisCategory : PreGaloisCategory (S2071CoverCategory X)]
  [galoisCategory : GaloisCategory (S2071CoverCategory X)]
  fiber : S2071CoverCategory X ⥤ FintypeCat
  [fiberFunctor : PreGaloisCategory.FiberFunctor fiber]
  fundamentalGroup : ProfiniteGrp
  action : ∀ Y : S2071CoverCategory X,
    MulAction fundamentalGroup (fiber.obj Y)
  isFundamentalGroup :
    letI (Y : S2071CoverCategory X) := action Y
    PreGaloisCategory.IsFundamentalGroup fiber fundamentalGroup
  geometricPiOne : ProfiniteGrp
  geometricConnectedness : Prop

end LeanFormal.IUT.XiFPaper.S2071CurveCardGaloisActual
end