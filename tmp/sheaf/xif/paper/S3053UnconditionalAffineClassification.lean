import tmp.sheaf.xif.paper.S3043AffineClassificationClosed

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3043AffineClassificationClosed
open LeanFormal.IUT.XiFPaper.S3041S3030IntegrationActual
open LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification
open LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo
open LeanFormal.IUT.XiFPaper.S3036IsDomainR0
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3053UnconditionalAffineClassification

/-- The bridge target is actual (via S3042). -/
theorem S3053_bridgeTarget : S3036BridgeTarget :=
  S3043_bridgeTarget

/-- R0 is a domain, unconditionally. -/
theorem S3053_r0_isDomain : IsDomain S3030AffineOriginClassification.R0 :=
  S3043_r0_isDomain

/-- Unconditional affine origin-preserving classification. -/
theorem S3053_affine_classification : S3030AffineOriginClassification :=
  S3043_affine_classification

/-- Same via the explicit S3042 bridge route. -/
theorem S3053_affine_classification_via_bridge : S3030AffineOriginClassification :=
  S3041_affine_classification_of_bridge S3053_bridgeTarget

/-- Projective S2888 classification remains conditional exactly on the chart-Z
transport. -/
theorem S3053_scheme_classification_of_transport
    (h : S3041SchemeClassFromAffine) :
    S2888OriginPreservingOrderTwoClassification :=
  S3043_scheme_classification_of_transport h

/-- Exact projective transport target. -/
def S3053ProjectiveTransportTarget : Prop := S3041SchemeClassFromAffine

#check S3053_bridgeTarget
#check S3053_r0_isDomain
#check S3053_affine_classification
#check S3053_affine_classification_via_bridge
#check S3053_scheme_classification_of_transport
#check S3053ProjectiveTransportTarget
#print axioms S3053_r0_isDomain
#print axioms S3053_affine_classification
#print axioms S3053_scheme_classification_of_transport

end LeanFormal.IUT.XiFPaper.S3053UnconditionalAffineClassification
end
