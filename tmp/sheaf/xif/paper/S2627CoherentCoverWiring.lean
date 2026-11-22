import tmp.sheaf.xif.paper.S2625D6CoverCancellationData
import tmp.sheaf.xif.paper.S1852CoherentCoverActual

/-! # S2627: CoherentCover wiring to D6CoverWithCancellation -/

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2619RightCancellationActual
open LeanFormal.IUT.XiFPaper.S2620M1CoherenceFields
open LeanFormal.IUT.XiFPaper.S2625D6CoverCancellationData

namespace LeanFormal.IUT.XiFPaper.S2627CoherentCoverWiring

universe u

/-- Coherent cover together with the two cancellation fields still needed by
M1.  The coherent part is the actual S1852 datum; the two fields are explicit. -/
structure CoherentCoverWithM1 where
  toCoherent : CoherentCover
  cancelRight : RightCancellation (CoherentCover.cover toCoherent).map
  cancelWitness : M1RightCancellationWitness (CoherentCover.cover toCoherent).map

/-- Forget the coherent structure and obtain the non-destructive D6 wrapper. -/
noncomputable def CoherentCoverWithM1.toD6
    (A : CoherentCoverWithM1) :
    D6CoverWithCancellation (CoherentCover.cover A.toCoherent) where
  cancelRight := A.cancelRight
  cancelWitness := A.cancelWitness

/-- Cover-level consumer: presentation with finite-etale projection. -/
noncomputable def presentationOfCoherentCover
    (A : CoherentCoverWithM1)
    {X : EtaleStackOverField S1726K}
    (m : X.Hom (CoherentCover.cover A.toCoherent).source)
    (T : SchemeOverField S1726K)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T)
      (CoherentCover.cover A.toCoherent).source.fiber)
    (Qy : EtaleStackBaseChangePresentation
      (CoherentCover.cover A.toCoherent).map T
      (Pseudofunctor.StrongTrans.vcomp ptY
        (CoherentCover.cover A.toCoherent).map))
    (Qx : EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.vcomp m
        (CoherentCover.cover A.toCoherent).map) T
      (Pseudofunctor.StrongTrans.vcomp ptY
        (CoherentCover.cover A.toCoherent).map))
    (hQyF : AlgebraicGeometry.IsFinite Qy.projection.left)
    (hQyE : AlgebraicGeometry.Etale Qy.projection.left)
    (hQxF : AlgebraicGeometry.IsFinite Qx.projection.left)
    (hQxE : AlgebraicGeometry.Etale Qx.projection.left) :
    Σ' P : EtaleStackBaseChangePresentation m T ptY,
      AlgebraicGeometry.IsFinite P.projection.left ∧
        AlgebraicGeometry.Etale P.projection.left :=
  presentationOfCover (A.toD6) m T ptY Qy Qx hQyF hQyE hQxF hQxE

#check CoherentCoverWithM1
#check CoherentCoverWithM1.toD6
#check presentationOfCoherentCover
#print axioms presentationOfCoherentCover

end LeanFormal.IUT.XiFPaper.S2627CoherentCoverWiring
end
