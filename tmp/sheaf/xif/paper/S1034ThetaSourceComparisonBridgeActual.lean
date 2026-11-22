import tmp.sheaf.xif.paper.S1033ThetaSourceComparisonAuditActual
import tmp.sheaf.xif.paper.S1027FinalActualInputActual
import tmp.sheaf.xif.paper.S994FiniteCarrierCor312Actual
import tmp.sheaf.xif.paper.S1025S994FiniteInputActual
import tmp.sheaf.xif.paper.S919GlobalWeightedInequalityActual
import tmp.sheaf.xif.paper.S1009HQHC3Actual

/-! # S1034: bridge from the actual S994 inequality to thetaSourceComparison

S994 gives the actual weighted inequality
  weightedPaperV T (s994VR T In) ≤ weightedPaperV T (s994VS T In)
for the actual S994FiniteInput In.  S1028/S1033 identify the link
identification with thetaSourceComparison.

To derive thetaSourceComparison from this inequality, the exact log-volume
identifications needed are
  -Oa.signedQPilotLogVolume = -weightedPaperV T (s994VR T In)
  P.procession.average      = -weightedPaperV T (s994VS T In).
They are recorded as an exact bridge; given them the comparison follows by
linarith.  No identification is asserted without proof. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1034ThetaSourceComparisonBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.ThetaLinkFromSource
open LeanFormal.IUT.XiFPaper.S1033ThetaSourceComparisonAuditActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S1025S994FiniteInputActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open LeanFormal.IUT.XiFPaper.S1009HQHC3Actual
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

/-- Exact log-volume identification bridge: the paper q-pilot magnitude and
the signed hull magnitude are the finite weighted S994 logs. -/
structure S1034LogVolumeBridge (In : S994FiniteInput T) where
  qPilotMagnitude_eq :
    -((s1009CanonicalOa (l := l) I C1 C2 C3).signedQPilotLogVolume) =
      -weightedPaperV T (s994VR (l := l) T In)
  hullMagnitude_eq :
    P.procession.average =
      -weightedPaperV T (s994VS (l := l) T In)

/-- Given the exact log-volume bridge, thetaSourceComparison follows from the
actual S994 weighted inequality. -/
theorem s1034ThetaSourceComparison_of_bridge
    (In : S994FiniteInput T)
    (hb : S1034LogVolumeBridge (l := l) I P T C1 C2 C3 In) :
    thetaSourceComparison (s1009CanonicalOa (l := l) I C1 C2 C3) P := by
  unfold thetaSourceComparison
  rw [hb.hullMagnitude_eq, hb.qPilotMagnitude_eq]
  have h := s994GlobalWeightedInequality (l := l) T In
  linarith

/-- Exact bridge existence required. -/
def S1034LogVolumeBridgeRequired : Prop :=
  ∃ In : S994FiniteInput T,
    Nonempty (S1034LogVolumeBridge (l := l) I P T C1 C2 C3 In)

/-- S1028/S1033 form: the same comparison is membership of the signed q-pilot
volume in the paper signed hull ray. -/
theorem s1034ThetaSourceComparison_iff_membership :
    thetaSourceComparison (s1009CanonicalOa (l := l) I C1 C2 C3) P ↔
      (s1009CanonicalOa (l := l) I C1 C2 C3).signedQPilotLogVolume ∈
        hullLogVolumeRay P.signedHullLogVolume :=
  s1033ThetaSourceComparison_iff_membership (l := l) I P C1 C2 C3

end LeanFormal.IUT.XiFPaper.S1034ThetaSourceComparisonBridgeActual

end
