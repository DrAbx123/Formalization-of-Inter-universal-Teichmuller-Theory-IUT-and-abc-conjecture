import tmp.sheaf.xif.paper.S2621FieldWithHypothesesActual
import tmp.sheaf.xif.paper.S1728CoverCategoryActual

/-! # S2625: non-destructive D6 cover cancellation wrapper -/

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
open LeanFormal.IUT.XiFPaper.S2619RightCancellationActual
open LeanFormal.IUT.XiFPaper.S2620M1CoherenceFields
open LeanFormal.IUT.XiFPaper.S2621FieldWithHypothesesActual

namespace LeanFormal.IUT.XiFPaper.S2625D6CoverCancellationData

universe u

/-- Non-destructive wrapper: a D6 cover together with the two global
right-cancellation fields needed by M1.  The foundation is untouched. -/
structure D6CoverWithCancellation (cover : S1728Cover) where
  cancelRight : RightCancellation cover.map
  cancelWitness : M1RightCancellationWitness cover.map

/-- The cover-level consumer: from the two cancellation fields, build the
base-changed presentation of `m` at `ptY` with finite-etale projection. -/
noncomputable def presentationOfCover
    {cover : S1728Cover}
    (W : D6CoverWithCancellation cover)
    {X : EtaleStackOverField S1726K} (m : X.Hom cover.source)
    (T : SchemeOverField S1726K)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) cover.source.fiber)
    (Qy : EtaleStackBaseChangePresentation cover.map T
      (Pseudofunctor.StrongTrans.vcomp ptY cover.map))
    (Qx : EtaleStackBaseChangePresentation
      (Pseudofunctor.StrongTrans.vcomp m cover.map) T
      (Pseudofunctor.StrongTrans.vcomp ptY cover.map))
    (hQyF : AlgebraicGeometry.IsFinite Qy.projection.left)
    (hQyE : AlgebraicGeometry.Etale Qy.projection.left)
    (hQxF : AlgebraicGeometry.IsFinite Qx.projection.left)
    (hQxE : AlgebraicGeometry.Etale Qx.projection.left) :
    Σ' P : EtaleStackBaseChangePresentation m T ptY,
      AlgebraicGeometry.IsFinite P.projection.left ∧
        AlgebraicGeometry.Etale P.projection.left := by
  let commutes := cancellationOf m cover.map W.cancelRight T ptY Qx
  let hpb := W.cancelWitness.cancelWitness m T ptY Qx commutes
  refine ⟨?P, ?_⟩
  · exact
      { pullbackScheme := Qx.pullbackScheme
        projection := Qx.projection
        projectionMap := Qx.projectionMap
        toSource := Qx.toSource
        commutes := commutes
        isPullback := hpb }
  · exact ⟨hQxF, hQxE⟩

#check D6CoverWithCancellation
#check presentationOfCover
#print axioms presentationOfCover

end LeanFormal.IUT.XiFPaper.S2625D6CoverCancellationData
end
