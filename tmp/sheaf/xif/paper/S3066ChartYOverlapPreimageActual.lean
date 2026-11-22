import tmp.sheaf.xif.paper.S3062ChartZPreservationProof
import tmp.sheaf.xif.paper.S2801E37ProjectiveClosure
import tmp.sheaf.xif.paper.S2820E37TransitionActual
import tmp.sheaf.xif.paper.S2844D6F6BaseChangeActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3062ChartZPreservationProof
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3066ChartYOverlapPreimageActual

abbrev e := S2820E37TransitionIso S2844D6F6BaseChangeActual.K

/-- Every chart-Y point in the overlap has a chart-Z preimage in the glued
scheme. -/
theorem S3066_chartYOverlapPreimage : S3062ChartYOverlapPreimage := by
  intro y hy
  obtain ⟨t, rfl⟩ := hy
  let D : Scheme.GlueData.{0} :=
    E37ProjGlueData S2844D6F6BaseChangeActual.K e
  refine ⟨E37ChartZOverlapMap S2844D6F6BaseChangeActual.K (e.inv t), ?_⟩
  change D.ι (ULift.up false)
      (E37ChartZOverlapMap S2844D6F6BaseChangeActual.K (e.inv t)) =
    D.ι (ULift.up true)
      (E37ChartYOverlapMap S2844D6F6BaseChangeActual.K t)
  rw [Scheme.GlueData.ι_eq_iff]
  refine ⟨e.inv t, rfl, ?_⟩
  change E37ChartYOverlapMap S2844D6F6BaseChangeActual.K (e.hom (e.inv t)) =
    E37ChartYOverlapMap S2844D6F6BaseChangeActual.K t
  have h : e.hom (e.inv t) = t := by
    have := congrArg (fun f => f t) e.inv_hom_id
    simpa using this
  rw [h]

#check S3066_chartYOverlapPreimage
#print axioms S3066_chartYOverlapPreimage

end LeanFormal.IUT.XiFPaper.S3066ChartYOverlapPreimageActual
end
