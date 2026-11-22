import LeanFormal.IUT.Audit.Status

/-! # S3137: paper-route field (c) region/volume — REUSE record

INDEX.PAPER-ROUTE.region-volume-weight (class B) reduced by the tree unit-region
Haar interface, hull finiteness, and CardHullReal Haar dilation-contraction
log-volume decomposition.  Exact reuse points recorded; no re-proving.
-/

namespace LeanFormal.IUT.XiFPaper.S3137PaperRouteFieldCRegionActual

/-- Reuse points for paper-route field (c). -/
def S3137PaperRouteFieldCReuse : List (String × String × String) :=
  [ ("unit-region Haar interface", "IQCarrierHaarData.lean:181 sourceUnitRegionHaarInterface", "REUSE: actual SourceUnitRegionHaarData from SourceImageRealization"),
    ("hull log-volume finiteness", "IQCarrierHaarData.lean:207/215 sourceUnitRegionHaarInterface_hull_logVolume_lt_top / _lower_bound_and_finiteness", "REUSE: thetaBound finiteness"),
    ("unit scaling interface", "IQCarrierHaarData.lean:265 sourceHullUnitScalingInterface", "REUSE/ADAPT: scaling normalization layer"),
    ("Cor312 conclusion from unit-region data", "IQCarrierHaarData.lean:353 sourceUnitRegionHaarData_cor312Conclusion", "REUSE"),
    ("Haar dilation-contraction decomposition", "CardHullRealHaarDilationDocking.lean:178 dilationContractionLogVolumeScaleDecomposition_logVolume_singleton_eq_logShell", "REUSE: scalar-factor/index side (F4 b1 and (c))"),
    ("unit region mass 1 / translated unit region", "HaarTranslateRealLineConsumerWiring.lean:127/132/140/165", "REUSE: real-line normalized test carrier"),
    ("source code (c) region reductions", "Cor312ComparisonGapReduction.lean:128/141/152/167/306 cor312Gap2_*", "REUSE: proved region reductions; per-triple point bound remains paper input"),
    ("designated (c) interface (mainline)", "Cor312ComparisonGapReduction.lean:306 cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound; mainline S3131Gap2ReductionReuseActual", "CONSUME: mainline-designated (c) interface (data + #check green)"),
    ("dictionary layer", "Cor312GapDictionaryLayer.lean:176/200/230/268/338/372", "REUSE: dictionary is a hypothesis (non-universality proved)") ]

theorem S3137PaperRouteFieldCReuse_length :
    S3137PaperRouteFieldCReuse.length = 9 := rfl

end LeanFormal.IUT.XiFPaper.S3137PaperRouteFieldCRegionActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: paper-route field (c) reuse. -/
def S3137PaperRouteFieldCRecord : Obligation :=
  { id := "INDEX.PAPER-ROUTE.region-volume-weight-reuse"
    source := "IQCarrierHaarData:181/207/215/265/353; CardHullRealHaarDilationDocking:178; HaarTranslateRealLineConsumerWiring:127/132/140/165; Cor312ComparisonGapReduction:128-306; Cor312GapDictionaryLayer:176-372"
    status := VerificationStatus.interface
    note := "FIELD (c) REUSE: the unit-region Haar interface, hull log-volume finiteness/lower bound, unit scaling interface, Cor312 conclusion from unit-region data, the Haar dilation-contraction log-volume decomposition, the normalized real-line test carrier, the proved gap-2 region reductions and the dictionary non-universality are already in tree. Remaining paper input: actual logShellPoint + nontrivial dictionary/point bound (class B). Not ABC-strength here."
    dependsOn := ["S3137PaperRouteFieldCRegionActual", "INDEX.PRIOR-ART.haar-log-volume", "INDEX.PRIOR-ART.f4-clause-hull"] }

end LeanFormal.IUT.Audit