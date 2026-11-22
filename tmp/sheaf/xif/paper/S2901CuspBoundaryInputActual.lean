import tmp.sheaf.xif.paper.S2894CuspFiveFieldsActual
import tmp.sheaf.xif.paper.S2887CorrectedCoreMinimalActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2894CuspFiveFieldsActual
open LeanFormal.IUT.XiFPaper.S2887CorrectedCoreMinimalActual
open LeanFormal.IUT.XiFPaper.S2873CuspGenericActual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2901CuspBoundaryInputActual

universe u
variable {F : Type u} [Field F]

/-- S2894 FiveFields plus the boundary predicate, exactly the GenericCuspData
field set, packaged for S2887. -/
structure S2901CuspInput (X : Iut.HyperbolicOrbicurve F) extends FiveFields X where
  isBoundary : forall object :
    X.stack.fiber.obj
      (LocallyDiscrete.mk (Opposite.op residueScheme)),
    IsEmpty
      ((openMap.app
          (LocallyDiscrete.mk (Opposite.op residueScheme))).toFunctor.obj
            object ≅
        Iut.OrbicurveFiniteEtaleCover.pointObject residueScheme point)

/-- Package into GenericCuspData; no field invented. -/
noncomputable def S2901CuspInput.toGenericCuspData
    {X : Iut.HyperbolicOrbicurve F} (I : S2901CuspInput X) :
    GenericCuspData X :=
  { compactification := I.compactification
    openMap := I.openMap
    openImmersion := I.openImmersion
    residueScheme := I.residueScheme
    point := I.point
    isBoundary := I.isBoundary }

/-- Forget the boundary predicate from a GenericCuspData. -/
noncomputable def S2901CuspInput.ofGenericCuspData
    {X : Iut.HyperbolicOrbicurve F} (D : GenericCuspData X) :
    S2901CuspInput X :=
  { compactification := D.compactification
    openMap := D.openMap
    openImmersion := D.openImmersion
    residueScheme := D.residueScheme
    point := D.point
    isBoundary := D.isBoundary }

/-- Any S2887 input already carries exactly this packaged cusp. -/
noncomputable def S2901CuspInput.ofS2887Input
    {signAction : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    (I : S2887Inputs signAction) : S2901CuspInput I.cK :=
  ofGenericCuspData I.cusp

/-- Replace the cusp field of S2887Inputs via the packaged S2901 input. -/
noncomputable def S2901WithCusp
    {signAction : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    (I : S2887Inputs signAction) (J : S2901CuspInput I.cK) :
    S2887Inputs signAction :=
  { I with cusp := J.toGenericCuspData }

#check S2901CuspInput
#check S2901CuspInput.toGenericCuspData
#check S2901CuspInput.ofGenericCuspData
#check S2901CuspInput.ofS2887Input
#check S2901WithCusp
#print axioms S2901CuspInput.toGenericCuspData
#print axioms S2901CuspInput.ofS2887Input

end LeanFormal.IUT.XiFPaper.S2901CuspBoundaryInputActual
end