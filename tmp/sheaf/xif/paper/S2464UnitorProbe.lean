import tmp.sheaf.xif.paper.S2459InvolutionSquaredActual
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
set_option synthInstance.maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
noncomputable section
open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans Bicategory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2459InvolutionSquaredActual

namespace LeanFormal.IUT.XiFPaper.S2464UnitorProbe
local notation "Xf" => S2482Orbicurve.stack.fiber

noncomputable def testLeft :
    (𝟙 Xf ≫ S2482EllipticInvolution : Xf ⟶ Xf) ≅ S2482EllipticInvolution :=
  Bicategory.leftUnitor (a := Xf) (b := Xf) S2482EllipticInvolution

noncomputable def testRight :
    (S2482EllipticInvolution ≫ 𝟙 Xf : Xf ⟶ Xf) ≅ S2482EllipticInvolution :=
  Bicategory.rightUnitor (a := Xf) (b := Xf) S2482EllipticInvolution

#print axioms testLeft
#print axioms testRight
end LeanFormal.IUT.XiFPaper.S2464UnitorProbe
end
