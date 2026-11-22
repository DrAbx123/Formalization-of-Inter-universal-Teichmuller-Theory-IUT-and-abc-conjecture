import tmp.sheaf.xif.paper.S2887CorrectedCoreMinimalActual
import tmp.sheaf.xif.paper.S2873CuspGenericActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2887CorrectedCoreMinimalActual
open LeanFormal.IUT.XiFPaper.S2873CuspGenericActual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open CategoryTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2894CuspFiveFieldsActual

universe u

variable {F : Type u} [Field F]

/-- The five geometric fields of `GenericCuspData` (everything except `isBoundary`). -/
structure FiveFields (X : Iut.HyperbolicOrbicurve F) where
  compactification : Iut.EtaleStackOverField F
  openMap : X.stack.Hom compactification
  openImmersion : Iut.EtaleStackOpenImmersion openMap
  residueScheme : Iut.SchemeOverField F
  point : Pseudofunctor.StrongTrans
    (Iut.schemeRepresentableEtalePseudofunctor F residueScheme)
    compactification.fiber

/-- Forget the boundary predicate. -/
def GenericCuspData.toFiveFields {X : Iut.HyperbolicOrbicurve F}
    (D : GenericCuspData X) : FiveFields X where
  compactification := D.compactification
  openMap := D.openMap
  openImmersion := D.openImmersion
  residueScheme := D.residueScheme
  point := D.point

variable (signAction : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve)

/-- The S2887 input already contains the generic cusp for `cK`. -/
noncomputable def S2894CuspFromS2887Input
    (I : S2887Inputs signAction) : GenericCuspData I.cK :=
  I.cusp

/-- Its five geometric fields. -/
noncomputable def S2894FiveFieldsFromS2887Input
    (I : S2887Inputs signAction) : FiveFields I.cK :=
  GenericCuspData.toFiveFields I.cusp

#check FiveFields
#check GenericCuspData.toFiveFields
#check S2894CuspFromS2887Input
#check S2894FiveFieldsFromS2887Input
#print axioms S2894CuspFromS2887Input
#print axioms S2894FiveFieldsFromS2887Input

end LeanFormal.IUT.XiFPaper.S2894CuspFiveFieldsActual
end
