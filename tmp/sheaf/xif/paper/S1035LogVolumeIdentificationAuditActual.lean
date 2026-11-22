import tmp.sheaf.xif.paper.S1034ThetaSourceComparisonBridgeActual
import tmp.sheaf.xif.paper.S1025S994FiniteInputActual
import tmp.sheaf.xif.paper.S1009HQHC3Actual
import tmp.sheaf.xif.paper.ThetaLinkFromSource
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.QPilotObjectActual
import tmp.sheaf.xif.paper.S919GlobalWeightedInequalityActual
import LeanFormal.IUT.Foundations.Volumes.WeightedVolume

/-! # S1035: audit of the bridge log-volume identifications

Definitions:
* Oa.signedQPilotLogVolume = localSignedLog Oa.line.C3.q (a single local scalar);
* weightedPaperV T v = sum over Bad places of nativeBadLocalWeight * v;
* P.procession.average = (sum over labels weight*value) / weightTotal.

These are not the same expression: signedQPilotLogVolume is neither a Bad-place
sum nor a label average, and s994VR/s994VS are finite-carrier log-measures.
Therefore no rfl/unfold identification exists; the exact bridge
S1034LogVolumeBridge remains required.  This file records the actual
unfoldings and the exact minimum, no fake equality. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1035LogVolumeIdentificationAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1034ThetaSourceComparisonBridgeActual
open LeanFormal.IUT.XiFPaper.S1009HQHC3Actual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.XiFPaper.S1025S994FiniteInputActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.ThetaLinkFromSource
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open MeasureTheory

universe uX uLabel uC3 uD3

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (C1 : SourceInputBinding I)
variable (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I)

/-- Actual definition: signed q-pilot log is the local scalar. -/
theorem s1035SignedQPilot_unfold :
    (s1009CanonicalOa I C1 C2 C3).signedQPilotLogVolume =
      localSignedLog (s1009CanonicalOa I C1 C2 C3).line.C3.q := rfl

/-- Actual definition: q-pilot magnitude is the negative local scalar. -/
theorem s1035QPilotMagnitude_eq :
    (s1009CanonicalOa I C1 C2 C3).qPilotLogMagnitude =
      - (s1009CanonicalOa I C1 C2 C3).signedQPilotLogVolume := rfl

/-- Actual definition: weightedPaperV is the Bad-place finite sum. -/
theorem s1035WeightedPaperV_unfold
    (v : Bad (nativePlaceSelection T) → Real) :
    weightedPaperV (l := l) T v =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * v b := rfl

/-- Actual definition: P.procession.average is the label weighted average. -/
theorem s1035ProcessionAverage_unfold :
    P.procession.average =
      (∑ j : label, P.procession.weight j * P.procession.value j) /
        P.procession.weightTotal := rfl

/-- Exact bridge required: no rfl identification between the local q-pilot
scalar/P-average and the finite weighted S994 logs. -/
def S1035BridgeRequired : Prop :=
  S1034LogVolumeBridgeRequired (l := l) I P T C1 C2 C3

end LeanFormal.IUT.XiFPaper.S1035LogVolumeIdentificationAuditActual

end
