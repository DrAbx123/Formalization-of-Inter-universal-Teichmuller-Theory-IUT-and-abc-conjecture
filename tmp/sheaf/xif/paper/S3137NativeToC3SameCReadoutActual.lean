import tmp.sheaf.xif.paper.S3137QThetaComparisonBridgeActual

/-!
# S3137: named residual for the same-C readout identifications of Batch A

Mainline (S3131PaperNormalizedComparisonActual) cannot prove, from its own
definitions, the two Stage-2 vs regional readout equalities:

  qPilotLogVolumeReading P = S3131PaperRegionalQ (l:=l) T mu
  thetaPilotHullLogVolumeReal C3 = S3131PaperRegionalHull (l:=l) T mu

they are cross-carrier same-C MODEL identifications between
(a) the single Stage-2 readings on (C3, P) from SourcePilotRegionData I and
    PaperQPilotObjectActual I, and
(b) the weighted sums over the native bad family Bad (nativePlaceSelection T)
    on the per-b qVFamTensorBlock T b with Remark 3.1.1(ii) weights.

This file names that residual exactly (NativeToC3SameCReadoutIdentification),
re-proves the conditional Cor 3.12 comparison from it, and records the missing
construction (a concrete native model, e.g. the S1280/Gaussian T with its
Stage-2 image (C3, P)) as a pending Audit obligation.  IUT III, Definition
3.8, (i) (p. 112); Proposition 3.9, (i) (p. 115); Corollary 3.12 (corpus
lines 10324--10353); Remark 3.1.1.  No carrier, no surrogate, no sorry,
no axiom.  WRITE-ONLY.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137NativeToC3SameCReadoutActual

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
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137QThetaComparisonBridgeActual
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

/-- **Exact named residual**: the native bad family T (with its per-place
qVFam tensor blocks and Remark 3.1.1(ii) weights) is the same fixed input C as
the Stage-2 pair (C3, P), read out on both sides.  This is a cross-carrier
same-C model identification; it is not constructed here. -/
def NativeToC3SameCReadoutIdentification : Prop :=
  SameCQThetaReadoutBridge (l := l) T mu C3 P

/-- **Corollary 3.12 signed comparison from the named same-C identification.** -/
theorem qThetaPilotLogVolumeComparison_of_nativeIdentification
    (B : NativeToC3SameCReadoutIdentification (l := l) T mu C3 P) :
    qThetaPilotLogVolumeComparison C3 P :=
  qThetaPilotLogVolumeComparison_of_sameC (l := l) T mu C3 P B

/-- **Magnitude form** |log Theta| <= |log q| from the named identification. -/
theorem qThetaMagnitudeComparison_of_nativeIdentification
    (B : NativeToC3SameCReadoutIdentification (l := l) T mu C3 P) :
    -thetaPilotHullLogVolumeReal C3 <= -qPilotLogVolumeReading P :=
  qThetaMagnitudeComparison_of_sameC (l := l) T mu C3 P B

end LeanFormal.IUT.XiFPaper.S3137NativeToC3SameCReadoutActual

namespace LeanFormal.IUT.Audit

/-- **Pending same-C readout identification (native bad family vs Stage-2 pair).**
The two equalities qPilotLogVolumeReading P = S3131PaperRegionalQ T mu and
thetaPilotHullLogVolumeReal C3 = S3131PaperRegionalHull T mu are cross-carrier
same-C model identifications between the weighted native bad family and the
single Stage-2 readings; mainline confirms they are not derivable from its
defs.  The missing construction is a concrete native model (S1280/Gaussian T
with its Stage-2 image (C3,P)). -/
def nativeToC3SameCReadoutIdentification : Obligation :=
  { id := "IUT-III.native-to-C3-same-C-readout-identification"
    source := "IUT III, Definition 3.8, (i), p. 112; Proposition 3.9, (i), p. 115; Remark 3.1.1; Corollary 3.12 (corpus 10324-10353)"
    status := VerificationStatus.pending
    note := "Two cross-carrier same-C equalities (q reading and Theta-hull reading vs mainline regional readouts).  Not constructed; the conditional Cor 3.12 comparison is proved in S3137NativeToC3SameCReadoutActual.  Concrete native model (S1280/Gaussian T with Stage-2 image) missing."
    dependsOn := ["S3137QThetaComparisonBridgeActual"] }

end LeanFormal.IUT.Audit