import tmp.sheaf.xif.paper.S3042R0Bridge
import tmp.sheaf.xif.paper.S3041S3030IntegrationActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3042R0Bridge
open LeanFormal.IUT.XiFPaper.S3041S3030IntegrationActual
open LeanFormal.IUT.XiFPaper.S3040GeneratedByXYActual
open LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification
open LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo
open LeanFormal.IUT.XiFPaper.S3036IsDomainR0
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3043AffineClassificationClosed

/-- The S3036 bridge target is actual (S3042). -/
theorem S3043_bridgeTarget : S3036BridgeTarget :=
  S3042_bridgeTarget

/-- R0 is actually a domain. -/
theorem S3043_r0_isDomain : IsDomain S3030AffineOriginClassification.R0 :=
  S3042_r0_isDomain

/-- The affine origin-preserving classification is now unconditional. -/
theorem S3043_affine_classification : S3030AffineOriginClassification :=
  S3040_affineOriginClassification S3043_r0_isDomain

/-- Same result through the S3041 bridge route. -/
theorem S3043_affine_classification_via_bridge : S3030AffineOriginClassification :=
  S3041_affine_classification_of_bridge S3043_bridgeTarget

/-- Projective S2888 classification from the explicit chart-Z transport. -/
theorem S3043_scheme_classification_of_transport
    (h : S3041SchemeClassFromAffine) :
    S2888OriginPreservingOrderTwoClassification :=
  S3041_scheme_classification_of_transport S3043_bridgeTarget h

#check S3043_bridgeTarget
#check S3043_r0_isDomain
#check S3043_affine_classification
#check S3043_affine_classification_via_bridge
#check S3043_scheme_classification_of_transport
#print axioms S3043_r0_isDomain
#print axioms S3043_affine_classification
#print axioms S3043_scheme_classification_of_transport

end LeanFormal.IUT.XiFPaper.S3043AffineClassificationClosed
end
