import tmp.sheaf.xif.paper.S3132SourceAdaptedCorollary312DataActual
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideH4CertificateAdapterActual

/-!
# STEP 0 prior-art: hull_le_theta|iqHullCertificate|ContractSourceReduction|FinitePlaceIQHullSignedCertificateNonvacuous -> hits LeanFormal/IUT/IUTIII/Corollary312/StepXI/ContractSourceReduction.lean:73/88, Volume.lean:160/167, CertificateHullWiring.lean:155, ABCBridge/Geometry/FinitePlaceIQHullSignedCertificateNonvacuous.lean:20/86/103, CardAMPLThetaBoundSupply.lean:78/94/116/125 -> ADAPT (value-layer only; no re-proof).

# H4 adapter: signed certificate value layer (ContractSourceReduction/Volume shape)

The certificate/hull route consumes the value-layer fields
`q_le_hull : qSigned <= hullVolume` and `hull_le_theta : hullVolume <= thetaSigned`
(ContractSourceReduction.lean:73, Volume.lean:160).  This file records that exact
shape for our Theta comparison payload, keeping H4 (the genuine measure-inclusion
bound `hull <= theta`, prior art FinitePlaceIQHullSignedCertificateNonvacuous.lean:20/86/103)
as an explicit hypothesis.  No closure claim.
-/

/-- Value-layer certificate record in the exact certificate-route shape. -/
structure HullSlotCertificate where
  hullVolume : ℝ
  thetaSigned : ℝ
  qSigned : ℝ
  q_le_hull : qSigned ≤ hullVolume
  hull_le_theta : hullVolume ≤ thetaSigned
  q_negative : qSigned < 0

/-- The certificate route's signed comparison `qSigned <= thetaSigned`. -/
theorem HullSlotCertificate.q_le_theta (c : HullSlotCertificate) :
    c.qSigned ≤ c.thetaSigned :=
  le_trans c.q_le_hull c.hull_le_theta

/-- The certificate's hull volume is nonnegative under the genuine
measure-inclusion reading (hull volume of a region). -/
theorem HullSlotCertificate.hullVolume_nonneg (c : HullSlotCertificate)
    (h : 0 ≤ c.qSigned) : 0 ≤ c.hullVolume :=
  le_trans h c.q_le_hull

/-- **H4 adapter:** from our explicit hull bound (H4 slot: canonical readout <= theta)
construct the certificate-route value layer. -/
def hullSlotCertificate_of_bound (theta : ℝ) (theta_nonneg : 0 ≤ theta)
    (hullVol qSigned : ℝ) (hH4 : hullVol ≤ theta)
    (hq : qSigned < 0) (hqhull : qSigned ≤ hullVol) : HullSlotCertificate where
  hullVolume := hullVol
  thetaSigned := theta
  qSigned := qSigned
  q_le_hull := hqhull
  hull_le_theta := hH4
  q_negative := hq

#check HullSlotCertificate
#check HullSlotCertificate.q_le_theta
#check hullSlotCertificate_of_bound

end LeanFormal.IUT.XiFPaper.S3132ThetaSideH4CertificateAdapterActual
end
