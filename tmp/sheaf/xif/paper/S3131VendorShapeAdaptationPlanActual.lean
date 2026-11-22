import LeanFormal.IUT.Audit.Status

/-! # S3131 vendor shape adaptation plan (SOURCE REFERENCE only; adapt not import) - data -/

namespace LeanFormal.IUT.XiFPaper.S3131VendorShapeAdaptationPlanActual

def S3131VendorShapeAdaptationPlan : List (String × String) :=
  [ ("vendor Iut/Stage1/IUTStage1IUTIVAlgebra.lean:8056 height_le_weighted_logDiff_logCond_minus_lowerBound (+:8085 data field)", "EXACT (b)/(c) shape 'height <= weighted logDiff/logCond - lowerBound' -> ADAPT (source reference only, not importable)"),
    ("vendor IUTStage1IUTIVAlgebra.lean:9900 genEll_transfer (+:9919 compact_subset_theoremA)", "formalized GenEll transfer interface shape -> CANDIDATE adaptation source"),
    ("vendor Iut/Stage1/IUTStage1HodgeSHE.lean:3996/4017 source_logVolume_le_target_logVolume / target_logVolume_le_source_logVolume (+:5936/:5970 logVolume_le)", "two-sided hull/image log-volume comparison for (c) -> ADAPT"),
    ("important", "vendor snapshot is SOURCE REFERENCE only; our files must restate the shapes in our namespace (no vendor import)") ]

theorem S3131VendorShapeAdaptationPlan_length : S3131VendorShapeAdaptationPlan.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.S3131VendorShapeAdaptationPlanActual