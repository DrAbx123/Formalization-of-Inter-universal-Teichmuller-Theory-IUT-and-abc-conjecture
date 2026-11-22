import tmp.sheaf.xif.paper.S3131NativeQCIdentificationActual
import tmp.sheaf.xif.paper.S3131PaperNormalizedComparisonActual
import tmp.sheaf.xif.paper.S3131CoefficientGapActual

/-! # S3131 Batch A axioms probe

Audit probe for the S3131 Batch A mainline files.  Every listed declaration
must have axioms within [propext, Classical.choice, Quot.sound].
-/

#print axioms LeanFormal.IUT.XiFPaper.S3131SameCSourceInputActual.qSourceFamily_qV
#print axioms LeanFormal.IUT.XiFPaper.S3131SameCSourceInputActual.weight_eq_inv
#print axioms LeanFormal.IUT.XiFPaper.S3131QCActualReadout.S3131QC_nonpos
#print axioms LeanFormal.IUT.XiFPaper.S3131QCActualReadout.S3131QC_eq_sourceData_normLog
#print axioms LeanFormal.IUT.XiFPaper.S3131HullActualReadout.S3131LocalQ_le_LocalHull
#print axioms LeanFormal.IUT.XiFPaper.S3131HullActualReadout.S3131LocalHull_nonpos
#print axioms LeanFormal.IUT.XiFPaper.S3131QCLeHCComparisonActual.S3131RegionalQC_le_RegionalHC
#print axioms LeanFormal.IUT.XiFPaper.S3131QCLeHCComparisonActual.S3131RegionalHC_nonpos
#print axioms LeanFormal.IUT.XiFPaper.S3131QCLeHCComparisonActual.S3131RegionalQC_le_RegionalHC_iff_magnitude
#print axioms LeanFormal.IUT.XiFPaper.S3131PaperNormalizedComparisonActual.S3131PaperQ_le_PaperHull
#print axioms LeanFormal.IUT.XiFPaper.S3131PaperNormalizedComparisonActual.S3131PaperRegionalQ_le_Hull
#print axioms LeanFormal.IUT.XiFPaper.S3131PaperNormalizedComparisonActual.S3131PaperRegionalQ_le_Hull_iff_magnitude
#print axioms LeanFormal.IUT.XiFPaper.S3131CoefficientGapActual.S3131CoefficientComparisonRequired_iff
#print axioms LeanFormal.IUT.XiFPaper.S3131CoefficientGapActual.S3131RootedCoefficientComparison_implies_unrooted
#print axioms LeanFormal.IUT.XiFPaper.S3131CoefficientGapActual.S3131QRegionContainedInHull_of_coefficient
#print axioms LeanFormal.IUT.XiFPaper.S3131NativeQCIdentificationActual.S3131RegionalQC_eq_nativeQC
#print axioms LeanFormal.IUT.XiFPaper.S3131NativeQCIdentificationActual.S3131QC_le_RegionalHC
