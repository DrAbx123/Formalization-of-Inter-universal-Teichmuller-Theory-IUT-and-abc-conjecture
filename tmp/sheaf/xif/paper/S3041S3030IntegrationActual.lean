import tmp.sheaf.xif.paper.S3040GeneratedByXYActual
import tmp.sheaf.xif.paper.S3036IsDomainR0
import tmp.sheaf.xif.paper.S2888OriginPreservingOrderTwo

noncomputable section
open LeanFormal.IUT
open CategoryTheory
open LeanFormal.IUT.XiFPaper.S3040GeneratedByXYActual
open LeanFormal.IUT.XiFPaper.S3036IsDomainR0
open LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification
open LeanFormal.IUT.XiFPaper.S2888OriginPreservingOrderTwo
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3041S3030IntegrationActual


/-- S3040 integrated with the S3036 domain bridge: affine origin-preserving
classification, conditional only on the bridge equivalence. -/
theorem S3041_affine_classification_of_bridge
    (h : S3036BridgeTarget) : S3030AffineOriginClassification :=
  S3040_affineOriginClassification (S3036_domain_of_bridge h)

/-- Direct form conditional on IsDomain R0. -/
theorem S3041_affine_classification_of_domain
    (hdom : IsDomain S3030AffineOriginClassification.R0) : S3030AffineOriginClassification :=
  S3040_affineOriginClassification hdom

/-- The projective scheme-level classification transported from the affine one.
The affine result classifies ring automorphisms of chart Z; transporting to the
glued scheme S2844X still requires chart-Z restriction and gluing. -/
def S3041SchemeClassFromAffine : Prop :=
  S3030AffineOriginClassification →
    S2888OriginPreservingOrderTwoClassification

/-- Conditional scheme-level classification via the affine result and explicit
projective transport. -/
theorem S3041_scheme_classification_of_transport
    (h : S3036BridgeTarget)
    (htransport : S3041SchemeClassFromAffine) :
    S2888OriginPreservingOrderTwoClassification :=
  htransport (S3041_affine_classification_of_bridge h)

/-!
## Integration status and first errors

Actual integration:
* S3041_affine_classification_of_bridge: S3040 + S3036_domain_of_bridge gives
  S3030AffineOriginClassification;
* S3041_affine_classification_of_domain: direct from IsDomain R0;
* S3041_scheme_classification_of_transport wires the affine classification into
  the S2888 projective classification once the transport is supplied.

First errors:
1. S3036BridgeTarget (R0 ring-equivalent to Mathlib's Weierstrass affine
   coordinate ring) is still unproved.  This is the only missing input for the
   affine classification.
2. S3041SchemeClassFromAffine: restriction of a scheme automorphism to chart Z
   and gluing back are not constructed.  The affine classification alone does
   not classify glued projective scheme automorphisms.
No transport or bridge is faked.
-/

#check S3041_affine_classification_of_bridge
#check S3041_affine_classification_of_domain
#check S3041SchemeClassFromAffine
#check S3041_scheme_classification_of_transport
#print axioms S3041_affine_classification_of_bridge
#print axioms S3041_scheme_classification_of_transport

end LeanFormal.IUT.XiFPaper.S3041S3030IntegrationActual
end
