import LeanFormal.IUT.Audit.Status

/-! # S3162: STEP 0 deep-search record (§7.10 paper-level focus)

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- STEP 0: queries -> hit summary -> decision rows. -/
def S3162Step0DeepSearch : List (String × String × String) := [
  ("height_le_weighted_logDiff|height_le_volume|volume_le_weight|genEll_transfer|thetaBound", "LeanFormal 4, paper 30, gap-exploration 2, vendor 24 hits", "REUSE/ADAPT: vendor IUTIVAlgebra:8056 height<=weight shape + :9900 genEll_transfer; paper artifacts S3135HeightVolumeReuse / S3135HeightWeightAtPaper / S3132IVGenEllShadowAdapter (genEll_transfer field)"),
  ("weight_le_theta|RegionRelativeToHullAndWeight|hpoint|hweightvol|uniform.*height.*volume", "LeanFormal 74, Iut 4, paper 204, vendor 44, corpus 1 hits", "REUSE: Cor312ComparisonGapReduction:306/316/383 regionVolume_le_normalizedWeight + hpoint; IQCarrierConcreteModel hpoint/hweightvol (:346/:386); S3137PaperRouteFieldCRegion hull finiteness"),
  ("GenEll Theorem 2.1", "corpus papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt Thm 2.1 (615-687); LeanFormal references 0 (shadow only)", "FORMALIZE statement form (class B target); shadow S3132IVGenEllShadowAdapterActual.genEll_transfer only a field/interface"),
  ("route bridges sameC/capsule-label/stage4-unit-map/invariance", "paper artifacts S3137PaperRouteMapActual / S3137PaperRouteFieldCRegionActual / S3136ModelAssemblyPipeline", "ADAPT: reuse existing route-bridge artifacts; do not re-prove") ]

theorem S3162Step0DeepSearch_length : S3162Step0DeepSearch.length = 4 := rfl

/-- STEP 0 deep-search record. -/
def S3162Step0DeepSearchRecord : Obligation :=
  { id := "IUT.project.step0-deep-search-paper-level"
    source := "§7.10 directive; tools/xif_deep_search.ps1 2026-11-10 05:32"
    status := VerificationStatus.interface
    note :=
      "STEP 0 prior-art (paper-level focus): (b) shape already in vendor/LeanFormal "
      ++ "(IUTIVAlgebra:8056 height<=weight; :9900 genEll_transfer) + paper adaptations; (c) hull "
      ++ "theta bound citable (Cor312ComparisonGapReduction:306 regionVolume_le_normalizedWeight) "
      ++ "+ hpoint/hweightvol in IQCarrierConcreteModel; GenEll Thm 2.1 present only in corpus "
      ++ "text (LeanFormal 0 references; shadow field). Decisions: REUSE/ADAPT, no re-proving; "
      ++ "GenEll statement formalization is a genuine paper-level target (class B)."
    dependsOn := [ "S3132IVGenEllShadowAdapterActual", "Cor312ComparisonGapReduction" ] }

#check S3162Step0DeepSearchRecord
#check S3162Step0DeepSearch_length

end LeanFormal.IUT.Audit
