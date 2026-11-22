import tmp.sheaf.xif.paper.S2620M1CoherenceFields

/-! # S2621: corrected BaseChangePresentationFieldWithHypotheses -/

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2618M1CancellationGoal
open LeanFormal.IUT.XiFPaper.S2619RightCancellationActual
open LeanFormal.IUT.XiFPaper.S2620M1CoherenceFields

namespace LeanFormal.IUT.XiFPaper.S2621FieldWithHypothesesActual

universe u

/-- The corrected consumer: given the two right-cancellation interfaces,
produce the presentation of `m` at `T`/`ptY` with finite-etale projection,
carrying the finite-etale hypotheses on the input presentations. -/
noncomputable def fieldWithHypothesesOfCancellation
    (cancelCommutes : ∀ {Y Z : EtaleStackOverField S1726K} (y : Y.Hom Z),
      RightCancellation y)
    (cancelWitness : ∀ {Y Z : EtaleStackOverField S1726K} (y : Y.Hom Z),
      M1RightCancellationWitness y) :
    BaseChangePresentationFieldWithHypotheses := by
  intro X Y Z m y T ptY Qy Qx hQyF hQyE hQxF hQxE
  let commutes := cancellationOf m y (cancelCommutes y) T ptY Qx
  let hpb := (cancelWitness y).cancelWitness m T ptY Qx commutes
  refine ⟨?P, ?_⟩
  · exact
      { pullbackScheme := Qx.pullbackScheme
        projection := Qx.projection
        projectionMap := Qx.projectionMap
        toSource := Qx.toSource
        commutes := commutes
        isPullback := hpb }
  · exact ⟨hQxF, hQxE⟩

#check fieldWithHypothesesOfCancellation
#print axioms fieldWithHypothesesOfCancellation

end LeanFormal.IUT.XiFPaper.S2621FieldWithHypothesesActual
end
