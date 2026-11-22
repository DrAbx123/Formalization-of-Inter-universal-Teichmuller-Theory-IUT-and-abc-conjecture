import tmp.sheaf.xif.paper.S3137R1RegistryCanonicalActual
import tmp.sheaf.xif.paper.S3137R1FinalStateActual

/-! Axiom probe for the task-53 registry overlay / final R1 state (data only). -/
open LeanFormal.IUT.Audit
open LeanFormal.IUT.XiFPaper.S3137QThetaComparisonBridgeActual
open LeanFormal.IUT.XiFPaper.S3137SameCModelMapResidualActual
open LeanFormal.IUT.XiFPaper.S3137GaussianR1ResidualLightActual
open LeanFormal.IUT.XiFPaper.S3137QThetaComparisonSummaryActual
open LeanFormal.IUT.XiFPaper.S3137C3TensorBlockDimensionActual

#print axioms S3137R1RegistryCanonical
#print axioms S3137R1ConsumerEdges
#print axioms S3137R1FinalState
#print axioms qThetaPilotLogVolumeComparison_of_sameC
#print axioms sameCQThetaReadoutBridge_of_modelMap
#print axioms gaussianR1ReducedResidual_residual_iff
#print axioms s3137_signed_comparison_summary
#print axioms c3TensorBlockDimension_eq_prod_finrank
