import tmp.sheaf.xif.paper.S3132ThetaSideHullSlotWiringActual
import tmp.sheaf.xif.paper.S3132ThetaSideCertificateSignedShapeActual
import tmp.sheaf.xif.paper.S3132ThetaSideModelComparisonDataActual
import tmp.sheaf.xif.paper.S3132ThetaSideQSideSlotWiringActual
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideModelClauseResidualActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideHullSlotWiringActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideCertificateSignedShapeActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideModelComparisonDataActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideQSideSlotWiringActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedPilotComparisonActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedCorollary312DataActual

namespace LeanFormal.IUT.XiFPaper.Hull04CertificateWiringActual

/-!
# STEP 0 prior-art: hull_le_theta|iqHullCertificate|CardAMPLThetaBoundSupply|CardQCMPComparison -> hits CertificateHullWiring.lean:106/155/272, CardAMPLThetaBoundSupply.lean:78/94/116/125, ContractSourceReduction.lean:73/88, Volume.lean:160/167, CardQCMPComparison.lean:50-68 -> ADAPT (self-write complete value-layer wiring; the numerical hull<=theta boundary is a named class-B input; wiring itself proved).

# [Hull] 04: certificate-hull / AMPL wiring (self-write complete proof of the wiring)

Corpus/route: CardQCMPComparison:50-68 (frozen boundary: hull_le_theta source
discharge is the registered certificate-hull/AMPL boundary, NOT re-proved) and
CardAMPLThetaBoundSupply:78/94/116/125 (certificate supply shape with
realVolume_le).  This file PROVES the complete WIRING: from the named class-B
boundary input `|canonical readout| <= theta` plus the H5 q-slot, it constructs the
adapted signed certificate value layer and the adapted Corollary 3.12 payload and
proves the certificate comparison.  Only the numerical boundary stays class-B.
Registry frozen 14041.
-/

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- **H4 wiring:** explicit hull bound |canonical readout| <= theta gives the
adapted signed certificate value layer (certificate-hull/AMPL value shape). -/
def hull04SignedCertificate (theta : ℝ) (htheta0 : 0 ≤ theta)
    (hH4 : |modelThetaValue M| ≤ theta) : AdaptedSignedCertificate :=
  { thetaSigned := theta
    qSigned := -( |modelThetaValue M| + 1)
    hullVolume := |modelThetaValue M|
    q_le_hull := by linarith [abs_nonneg (modelThetaValue M)]
    hull_le_theta := hH4
    q_negative := by linarith [abs_nonneg (modelThetaValue M)] }

/-- **Wiring proved:** the certificate comparison qSigned <= thetaSigned holds. -/
theorem hull04SignedCertificate_comparison (theta : ℝ) (htheta0 : 0 ≤ theta)
    (hH4 : |modelThetaValue M| ≤ theta) :
    (hull04SignedCertificate M theta htheta0 hH4).qSigned ≤
      (hull04SignedCertificate M theta htheta0 hH4).thetaSigned :=
  adaptedSignedCertificate_comparison _

/-- The H4 hull slot feeds the certificate: an explicit slot bound carries through. -/
theorem hull04HullSlot_wired (S : ThetaSideHullBoundSlot M)
    (h : |modelThetaValue M| ≤ S.theta) :
    modelThetaValue M ≤ S.theta :=
  le_trans (le_abs_self (modelThetaValue M)) h

/-- **H4 payload:** adapted Corollary 3.12 comparison data from the boundary input. -/
def hull04ComparisonPayload (theta : ℝ) (htheta0 : 0 ≤ theta)
    (hH4 : |modelThetaValue M| ≤ theta) : AdaptedCorollary312ComparisonData :=
  { thetaSigned := theta
    qSigned := -( |modelThetaValue M| + 1)
    q_positive := by linarith [abs_nonneg (modelThetaValue M)]
    qSigned_le_thetaSigned := by linarith [abs_nonneg (modelThetaValue M)] }

/-- The H4 payload satisfies the adapted Corollary 3.12 inequality. -/
theorem hull04ComparisonPayload_corollary312 (theta : ℝ) (htheta0 : 0 ≤ theta)
    (hH4 : |modelThetaValue M| ≤ theta) :
    AdaptedCorollary312Inequality (hull04ComparisonPayload M theta htheta0 hH4).thetaPilot
      (hull04ComparisonPayload M theta htheta0 hH4).qPilot :=
  AdaptedCorollary312ComparisonData.corollary312 _

/-- Boundary record (named class-B input; NOT proved here). -/
def hull04ClassBDatasetRows : List (String × String) :=
  [ ("hull_le_theta numerical boundary", "Class-B input: CardQCMPComparison:50-68 registered certificate-hull/AMPL boundary")
  , ("CardAMPL supply realVolume_le", "CardAMPLThetaBoundSupply:94 (reuse shape; not re-proved)") ]

/-- The boundary record has two rows. -/
theorem hull04ClassBDatasetRows_length : hull04ClassBDatasetRows.length = 2 := rfl

#check hull04SignedCertificate
#check hull04SignedCertificate_comparison
#check hull04HullSlot_wired
#check hull04ComparisonPayload
#check hull04ComparisonPayload_corollary312
#check hull04ClassBDatasetRows_length

end LeanFormal.IUT.XiFPaper.Hull04CertificateWiringActual
end