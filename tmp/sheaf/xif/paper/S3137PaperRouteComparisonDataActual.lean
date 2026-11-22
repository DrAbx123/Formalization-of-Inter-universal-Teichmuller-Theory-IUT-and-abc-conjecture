import tmp.sheaf.xif.paper.S3137QThetaComparisonBridgeActual
import LeanFormal.IUT.Audit.Status

/-! # S3137: paper-route comparison data in vendor CorollarySchema shape

Mirrors promachina Iut/Stage1/CorollarySchema.lean:49-83 Corollary312ComparisonData
(thetaSigned, qSigned, q_positive : 0 < -qSigned, qSigned_le_thetaSigned) as the
LOCAL acceptance shape for INDEX.PAPER-ROUTE, constructed from the actual Stage-2
qTheta comparison plus q-pilot positivity.  Vendor is source-only (not imported).
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3137PaperRouteComparisonDataActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137QThetaComparisonBridgeActual
open LeanFormal.IUT.Audit
open MeasureTheory

variable {l : PrimeGeFive}
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- Vendor-shaped signed comparison payload for Corollary 3.12. -/
structure S3137Corollary312ComparisonData where
  thetaSigned : Real
  qSigned : Real
  q_positive : 0 < -qSigned
  qSigned_le_thetaSigned : qSigned <= thetaSigned

/-- Construct the payload from the actual qTheta comparison + positivity. -/
def S3137Corollary312ComparisonData.ofQTheta
    (hcmp : qThetaPilotLogVolumeComparison C3 P)
    (hpos : 0 < -qPilotLogVolumeReading P) :
    S3137Corollary312ComparisonData where
  thetaSigned := thetaPilotHullLogVolumeReal C3
  qSigned := qPilotLogVolumeReading P
  q_positive := hpos
  qSigned_le_thetaSigned := hcmp

/-- The constructed payload's signed inequality is the qTheta comparison. -/
theorem S3137Corollary312ComparisonData.ofQTheta_signed
    (hcmp : qThetaPilotLogVolumeComparison C3 P)
    (hpos : 0 < -qPilotLogVolumeReading P) :
    (S3137Corollary312ComparisonData.ofQTheta C3 P hcmp hpos).qSigned <=
      (S3137Corollary312ComparisonData.ofQTheta C3 P hcmp hpos).thetaSigned :=
  hcmp

/-- Corollary 3.12 projection (vendor corollary312 analogue). -/
theorem S3137Corollary312ComparisonData.corollary312
    (d : S3137Corollary312ComparisonData) :
    d.qSigned <= d.thetaSigned :=
  d.qSigned_le_thetaSigned

end LeanFormal.IUT.XiFPaper.S3137PaperRouteComparisonDataActual

namespace LeanFormal.IUT.Audit

/-- INDEX: paper-route comparison data (vendor shape adapted). -/
def INDEX_PAPER_ROUTE_comparisonData : Obligation :=
  { id := "INDEX.PAPER-ROUTE.comparison-data-vendor-shape"
    source := "vendor/promachina/snapshots/1fa6387f.../Iut/Stage1/CorollarySchema.lean:49-83; S3137 qTheta comparison; S3137QThetaPilotLogVolumeReadingsActual"
    status := VerificationStatus.interface
    note := "ADAPTED VENDOR SHAPE (source-only, not imported): S3137Corollary312ComparisonData with ofQTheta constructor from the actual qTheta comparison + q-pilot positivity; corollary312 projection. Mirrors promachina Corollary312ComparisonData/corollary312 for the paper-route acceptance shape. Consumer: mainline paper route field (b). Not ABC-strength; not a residual itself."
    dependsOn := ["S3137PaperRouteComparisonDataActual", "INDEX.PAPER-ROUTE.height-comparison"] }

end LeanFormal.IUT.Audit
