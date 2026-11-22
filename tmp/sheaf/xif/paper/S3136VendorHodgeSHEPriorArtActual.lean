/-! # Stage-4 host: vendor prior-art shapes for the (c) split-point side

PRIOR ART (source reference only; vendor snapshot is a separate lake project and is
NOT imported): vendor/promachina/snapshots/1fa6387f11fb6dc67eb618b8138e6bc64f56b039/
* Iut/Stage1/IUTStage1HodgeSHE.lean:3996 IUTStage1NonarchimedeanInclusionData field
  source_logVolume_le_target_logVolume : sourceLogVolume.finiteLogVolume <= targetLogVolume.finiteLogVolume;
  :4017 IUTStage1ArchimedeanSurjectionData field target_logVolume_le_source_logVolume;
  :5936 theorem logVolume_le (nonarchimedean inclusion), :5970 theorem logVolume_le
  (archimedean surjection) - two-sided source/target log-volume comparisons as DATA
  FIELDS of the stage model.
* Iut/Stage1/IUTStage1IUTIVAlgebra.lean:8056 theorem
  height_le_weighted_logDiff_logCond_minus_lowerBound (data :
  IUTStage1IUTIVTheoremABoundedDiscrepancyShadow Point) (x) :
  data.height x <= (1+eps)*(logDiff x + logCond x) - lowerBound (from the data's
  discrepancy_lower_bound field).

DETERMINATION: the vendor comparisons are DATA FIELDS of model structures (the
comparison is assumed, not proved); our LeanFormal chain instead proves the same
two-sided shapes from the carrier fields where possible
(e.g. scaleShift_unitRegion_logVolume_le, logVolume_mono) and keeps the analytic
estimates as class B.  Adapt: use the vendor shape names in the paper-input ledger;
do not import or claim discharge.

LABEL: vendor source-reference survey (data). Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136VendorHodgeSHEPriorArtActual

structure LGPVendorComparisonRow where
  location : String
  declaration : String
  shape : String
  decision : String

def lgPVendorComparisonRows : List LGPVendorComparisonRow :=
  [ ⟨"IUTStage1HodgeSHE.lean:3996", "IUTStage1NonarchimedeanInclusionData.source_logVolume_le_target_logVolume", "sourceLogVolume.finiteLogVolume <= targetLogVolume.finiteLogVolume (data field)", "ADAPT shape to paper-input ledger; data field, no discharge"⟩,
    ⟨"IUTStage1HodgeSHE.lean:4017", "IUTStage1ArchimedeanSurjectionData.target_logVolume_le_source_logVolume", "targetLogVolume.finiteLogVolume <= sourceLogVolume.finiteLogVolume (data field)", "ADAPT shape; two-sided counterpart"⟩,
    ⟨"IUTStage1HodgeSHE.lean:5936/:5970", "logVolume_le (nonarchimedean inclusion / archimedean surjection)", "projections of the two-sided comparison fields", "ADAPT shape"⟩,
    ⟨"IUTStage1IUTIVAlgebra.lean:8056", "height_le_weighted_logDiff_logCond_minus_lowerBound", "height <= (1+eps)(logDiff+logCond) - lowerBound from the bounded-discrepancy shadow field", "ADAPT shape for the Thm A endpoint; field is data, not proved"⟩ ]

theorem lgPVendorComparisonRows_length : lgPVendorComparisonRows.length = 4 := rfl

#check lgPVendorComparisonRows
#check lgPVendorComparisonRows_length

end LeanFormal.IUT.XiFPaper.S3136VendorHodgeSHEPriorArtActual