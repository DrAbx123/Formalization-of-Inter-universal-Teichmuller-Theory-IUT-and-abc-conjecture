import tmp.sheaf.xif.paper.S3137SameCModelMapResidualActual
import tmp.sheaf.xif.paper.S3137QThetaComparisonSummaryActual

/-!
# S3137: short consumer aliases for the R1 chain (task-53)

Single import point for downstream consumers (gate, shehdd canonical rooted
target, hull Theta-half): short-named aliases of the green R1 consumer
declarations.  No new proof content; aliases only.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137R1ConsumerAliasActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131QCLeHCComparisonActual
open LeanFormal.IUT.XiFPaper.S3131PaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.S3131SameCSourceInputActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137QThetaComparisonBridgeActual
open LeanFormal.IUT.XiFPaper.S3137SameCModelMapResidualActual
open LeanFormal.IUT.XiFPaper.S3137NativeToC3SameCReadoutActual
open LeanFormal.IUT.XiFPaper.S3137QThetaComparisonSummaryActual
open MeasureTheory

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [forall b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
variable (mu : forall b : Bad (nativePlaceSelection T),
  Measure (qVFamTensorBlock T b))
variable [forall b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- R1 consumer alias: native-to-C3 identity from the model-map residual. -/
theorem r1_nativeIdentification
    (M : SameCModelMapResidual (l := l) T mu C3 P) :
    NativeToC3SameCReadoutIdentification (l := l) T mu C3 P :=
  nativeToC3Identification_of_modelMap (l := l) T mu C3 P M

/-- R1 consumer alias: signed Cor 3.12 comparison from the model-map residual. -/
theorem r1_signedComparison
    (M : SameCModelMapResidual (l := l) T mu C3 P) :
    qThetaPilotLogVolumeComparison C3 P :=
  qThetaPilotLogVolumeComparison_of_modelMap (l := l) T mu C3 P M

/-- R1 consumer alias: magnitude form |log Theta| <= |log q|. -/
theorem r1_magnitudeComparison
    (M : SameCModelMapResidual (l := l) T mu C3 P) :
    -thetaPilotHullLogVolumeReal C3 <= -qPilotLogVolumeReading P :=
  qThetaMagnitudeComparison_of_modelMap (l := l) T mu C3 P M

/-- R1 consumer alias: signed comparison directly from the named same-C
identification. -/
theorem r1_signedComparison_of_nativeIdentification
    (B : NativeToC3SameCReadoutIdentification (l := l) T mu C3 P) :
    qThetaPilotLogVolumeComparison C3 P :=
  s3137_signed_comparison_summary (l := l) T mu C3 P B

end LeanFormal.IUT.XiFPaper.S3137R1ConsumerAliasActual

#check LeanFormal.IUT.XiFPaper.S3137R1ConsumerAliasActual.r1_nativeIdentification
#check LeanFormal.IUT.XiFPaper.S3137R1ConsumerAliasActual.r1_signedComparison
#check LeanFormal.IUT.XiFPaper.S3137R1ConsumerAliasActual.r1_magnitudeComparison