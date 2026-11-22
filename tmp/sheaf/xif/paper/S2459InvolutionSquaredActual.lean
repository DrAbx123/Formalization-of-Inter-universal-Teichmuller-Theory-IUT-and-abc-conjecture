import tmp.sheaf.xif.paper.S2482QiInvolutionSquareActual
import tmp.sheaf.xif.paper.S2482QiOrbicurveActual
import tmp.sheaf.xif.paper.S2482QiInvolutionActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionSquareActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2459InvolutionSquaredActual

/-- The actual orbicurve-level square of the elliptic involution. -/
abbrev S2459InvolutionSquared :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp
        S2482EllipticInvolution S2482EllipticInvolution)
      (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve) :=
  S2482EllipticInvolution_square

/-- Exact missing field of OrbicurveSignAction: its pseudofunctor diagram. -/
def S2459DiagramMissing : Prop :=
  Nonempty (Pseudofunctor Iut.SignActionIndex (Iut.EtaleStackPseudofunctor F))

#print axioms S2459InvolutionSquared

end LeanFormal.IUT.XiFPaper.S2459InvolutionSquaredActual

end
