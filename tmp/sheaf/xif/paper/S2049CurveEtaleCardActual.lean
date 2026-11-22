import tmp.sheaf.xif.paper.S2048CurvePiOneActual
import LeanFormal.IUT.Foundations.Geometry.CurveEtaleFundamentalGroup

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2049CurveEtaleCardActual
open LeanFormal.IUT
open LeanFormal.IUT.Foundations.Geometry
open CategoryTheory AlgebraicGeometry

universe u

/-- Actual finite etale cover category of a curve scheme. -/
abbrev S2049CoverCategory (X : Scheme.{u}) : Type (u + 1) :=
  FiniteEtaleCover X

/-- Actual geometric fiber functor at a chosen geometric point. -/
abbrev S2049FiberFunctor (X : Scheme.{u}) (Omega : Type u) [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ X) :
    S2049CoverCategory X ⥤ Type u :=
  geometricFiberFunctor Omega x

/-- Actual automorphism group of the geometric fiber functor. -/
abbrev S2049AutGroup (X : Scheme.{u}) (Omega : Type u) [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ X) : Type (u + 1) :=
  curveEtaleFundamentalGroup Omega x

/-- Exact first missing completion of the actual cover category/fiber functor
to the frozen Example36 card. -/
structure S2049CardCompletion (X : Scheme.{u}) where
  [galoisCategory : GaloisCategory (S2049CoverCategory X)]
  fiber : S2049CoverCategory X ⥤ FintypeCat
  [fiberFunctor : PreGaloisCategory.FiberFunctor fiber]
  fundamentalGroup : ProfiniteGrp
  action : ∀ Y : S2049CoverCategory X,
    MulAction fundamentalGroup (fiber.obj Y)
  isFundamentalGroup :
    letI (Y : S2049CoverCategory X) := action Y
    PreGaloisCategory.IsFundamentalGroup fiber fundamentalGroup
  geometricPiOne : ProfiniteGrp
  geometricConnectedness : Prop

end LeanFormal.IUT.XiFPaper.S2049CurveEtaleCardActual
end