import tmp.sheaf.xif.paper.S3137QThetaComparisonBridgeActual
import tmp.sheaf.xif.paper.S3137NativeToC3SameCReadoutActual
import LeanFormal.IUT.Audit.Status

/-!
# S3137: final q/Theta comparison summary (Stage-2 container)

Single consumer entry point for downstream streams: from the named same-C
readout identification (R1 residual Prop), the signed Cor 3.12 comparison and
its magnitude form follow via mainline's unconditional same-normalization
paper-normalized comparison.  The normalization caveat (raw log-Haar vs
degree-normalized V-form; Q_p-spectral vs default-residue coefficient) is
recorded as the pending obligation IUT-III.q-theta-paper-normalization-bridge.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137QThetaComparisonSummaryActual

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
open LeanFormal.IUT.XiFPaper.S3137NativeToC3SameCReadoutActual
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

/-- **Final signed comparison summary** from the R1 same-C readout
identification. -/
theorem s3137_signed_comparison_summary
    (B : NativeToC3SameCReadoutIdentification (l := l) T mu C3 P) :
    qThetaPilotLogVolumeComparison C3 P :=
  qThetaPilotLogVolumeComparison_of_nativeIdentification (l := l) T mu C3 P B

/-- **Final magnitude comparison summary** |log Theta| <= |log q| from the R1
same-C readout identification. -/
theorem s3137_magnitude_comparison_summary
    (B : NativeToC3SameCReadoutIdentification (l := l) T mu C3 P) :
    -thetaPilotHullLogVolumeReal C3 <= -qPilotLogVolumeReading P :=
  qThetaMagnitudeComparison_of_nativeIdentification (l := l) T mu C3 P B

end LeanFormal.IUT.XiFPaper.S3137QThetaComparisonSummaryActual
