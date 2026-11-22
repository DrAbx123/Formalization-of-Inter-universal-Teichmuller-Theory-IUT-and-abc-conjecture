import tmp.sheaf.xif.paper.S3132ThetaSideSharpResidualReducedActual
import tmp.sheaf.xif.paper.S3132ThetaSideComparisonRegionBundleActual
import tmp.sheaf.xif.paper.S3132ThetaSideModelComparisonDataActual
import tmp.sheaf.xif.paper.S3132SourceAdaptedPilotComparisonActual
import tmp.sheaf.xif.paper.S3132SourceAdaptedCorollary312DataActual
import tmp.sheaf.xif.paper.S3136ModelSourceClauseActual
import tmp.sheaf.xif.paper.S3136ModelNativeDataWithHaarActual
import tmp.sheaf.xif.paper.S3132RootedScalingDataFormulaActual
import Mathlib.Tactic.Linarith

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
open LeanFormal.IUT.XiFPaper.S3132RootedScalingDataTrivialActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideModelClauseResidualActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideSharpResidualReducedActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideModelComparisonDataActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideComparisonRegionBundleActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedPilotComparisonActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedCorollary312DataActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideCertificateSignedShapeActual

/-!
# Theta-side signed certificate shape (adapted value layer)

PRIOR ART (one line): LeanFormal/IUT/IUTIII/Corollary312/StepXI/CertificateHullWiringSigned.lean:132
structure StepXIFiniteCertificateSigned {hull/weighted/qSigned/thetaSigned/q_le_hull/hull_le_theta/q_negative}
-> ADAPT the VALUE-LAYER fields only (hullVolume as a real number); the FiniteHull/WeightedValues
construction is NOT re-proved here.

This gives the Theta comparison payload the exact signed-certificate field shape used by the
certificate/hull route (CertificateHullWiring.lean:155 iqHullCertificate; :272 sourceRealHullVolume_le_theta),
with the hull volume slot left as an explicit H4 hypothesis (no closure claim).
-/

/-- Value-layer signed certificate shape (adapted from StepXIFiniteCertificateSigned). -/
structure AdaptedSignedCertificate where
  /-- signed Theta value (negative of the positive-magnitude canonical readout) -/
  thetaSigned : ℝ
  /-- signed q value -/
  qSigned : ℝ
  /-- the hull volume slot (canonical Theta magnitude in our application) -/
  hullVolume : ℝ
  q_le_hull : qSigned ≤ hullVolume
  hull_le_theta : hullVolume ≤ thetaSigned
  q_negative : qSigned < 0

/-- The adapted certificate satisfies the signed comparison shape used by the
certificate route: qSigned <= thetaSigned (Volume.lean:160/167 shape). -/
theorem adaptedSignedCertificate_comparison (c : AdaptedSignedCertificate) :
    c.qSigned ≤ c.thetaSigned :=
  le_trans c.q_le_hull c.hull_le_theta

/-- The same comparison in the negated presentation `-theta.value <= -q.value`
used for the vendor-schema signed payload (both sides negative). -/
theorem adaptedSignedCertificate_comparison_neg (c : AdaptedSignedCertificate) :
    -c.thetaSigned ≤ -c.qSigned :=
  neg_le_neg (adaptedSignedCertificate_comparison c)

#check AdaptedSignedCertificate
#check adaptedSignedCertificate_comparison
#check adaptedSignedCertificate_comparison_neg


end LeanFormal.IUT.XiFPaper.S3132ThetaSideCertificateSignedShapeActual
end