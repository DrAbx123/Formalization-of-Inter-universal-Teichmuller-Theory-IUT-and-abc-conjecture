import tmp.sheaf.xif.paper.S3139PriorArtAudit2Actual
import tmp.sheaf.xif.paper.S3139ModelM1DischargeActual
import tmp.sheaf.xif.paper.S3139HaarModelConsumptionActual
import tmp.sheaf.xif.paper.S3139RouteResidualUpdateV3Actual
import tmp.sheaf.xif.paper.S3139VendorSourceCoreEstimatesActual
import tmp.sheaf.xif.paper.S3139RouteModelIdsActual

-- S3139 model-route probe: Option-B M1 discharge, tree-model/CardHull consumption,
-- residual list v3, vendor source-core estimates, model-route ids.

#print axioms LeanFormal.IUT.XiFPaper.S3139ModelM1DischargeActual.sourceModelM1Evidence_holds
#print axioms LeanFormal.IUT.XiFPaper.S3139ModelM1DischargeActual.firstTriangleRouteResidualModelM1_placeSelection
#print axioms LeanFormal.IUT.XiFPaper.S3139HaarModelConsumptionActual.s3139_treeModelHaarData_scaling
#print axioms LeanFormal.IUT.XiFPaper.S3139HaarModelConsumptionActual.s3139_treeModel_theta_q
#print axioms LeanFormal.IUT.XiFPaper.S3139HaarModelConsumptionActual.s3139_modelHullVolume_le_imageVolume
#print axioms LeanFormal.IUT.XiFPaper.S3139HaarModelConsumptionActual.sourceModelRouteEvidence
#print axioms LeanFormal.IUT.XiFPaper.S3139VendorSourceCoreEstimatesActual.sourceLocalContainerLogVolumeEstimateOf
#print axioms LeanFormal.IUT.XiFPaper.S3139VendorSourceCoreEstimatesActual.sourceLocalObjectContainerLogVolumeEstimateOf
#print axioms LeanFormal.IUT.XiFPaper.S3139PriorArtAudit2Actual.modelRoutePriorArt
#print axioms LeanFormal.IUT.XiFPaper.S3139RouteResidualUpdateV3Actual.routeOpenResidualsV3
#print axioms LeanFormal.IUT.XiFPaper.S3139RouteModelIdsActual.routeModelIds
