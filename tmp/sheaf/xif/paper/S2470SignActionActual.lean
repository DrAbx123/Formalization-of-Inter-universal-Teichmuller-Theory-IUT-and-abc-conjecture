import tmp.sheaf.xif.paper.S2469AtBaseActual

noncomputable section
open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans Bicategory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2459InvolutionSquaredActual
open LeanFormal.IUT.XiFPaper.S2468DiagramSubsingletonActual
open LeanFormal.IUT.XiFPaper.S2469AtBaseActual
set_option synthInstance.maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2470SignActionActual
local notation "Xf" => S2482Orbicurve.stack.fiber

noncomputable def S2470SignAction : Iut.OrbicurveSignAction S2482Orbicurve where
  diagram := S2468Diagram
  atBase := S2469AtBase
  inversion := S2482EllipticInvolution
  generator_identification := by
    change (𝟙 Xf ≫ S2482EllipticInvolution) ≫ 𝟙 Xf ≅ S2482EllipticInvolution
    exact (Bicategory.rightUnitor (a := Xf) (b := Xf)
        (𝟙 Xf ≫ S2482EllipticInvolution)).trans
      (Bicategory.leftUnitor (a := Xf) (b := Xf) S2482EllipticInvolution)
  inversionSquared := S2459InvolutionSquared

#print axioms S2470SignAction

end LeanFormal.IUT.XiFPaper.S2470SignActionActual
end
