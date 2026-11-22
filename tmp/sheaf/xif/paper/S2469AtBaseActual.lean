import tmp.sheaf.xif.paper.S2468DiagramSubsingletonActual
import tmp.sheaf.xif.paper.S2433NonidentityStrongRepresentable
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

noncomputable section
open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans Bicategory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2459InvolutionSquaredActual
open LeanFormal.IUT.XiFPaper.S2468DiagramSubsingletonActual
set_option synthInstance.maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2469AtBaseActual
local notation "Xf" => S2482Orbicurve.stack.fiber

noncomputable def S2469AtBase :
    Bicategory.Equivalence (S2468Diagram.obj Iut.signActionObject) Xf :=
  Bicategory.Equivalence.id Xf

#check S2469AtBase
#print axioms S2469AtBase

end LeanFormal.IUT.XiFPaper.S2469AtBaseActual
end
