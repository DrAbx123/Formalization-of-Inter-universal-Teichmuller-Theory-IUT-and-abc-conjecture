import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3131PaperNormalizedComparisonActual
import LeanFormal.IUT.Audit.Status

/-!
# S3137: same-C bridge from the Stage-2 actual container to the Batch A comparison

IUT III, Corollary 3.12 (corpus lines 10324--10353; Step (xi-f)): the signed
comparison of the q-pilot and Theta-pilot log-volumes.  On the Stage-2 actual
objects this file has (S3137QThetaPilotLogVolumeReadingsActual):

* q-pilot reading qPilotLogVolumeReading P = P.signedQPilotLogVolume = -|log q|;
* Theta-side container reading thetaPilotHullLogVolumeReal C3 = actual Haar
  log-volume of the actual lambda-O hull of the actual C3 tensor log-shell
  region (which equals the region); its p-scaling is the packet normalization
  (S3137ThetaHullVolumeScalingActual).

The Batch A mainline has the unconditional paper-normalized regional comparison
on the fixed input C (S3131PaperNormalizedComparisonActual):

  S3131PaperRegionalQ T mu <= S3131PaperRegionalHull T mu.

This file states the exact remaining same-C identification as the structure
SameCQThetaReadoutBridge (the two Stage-2 readings equal the two regional
readouts) and PROVES that, given that bridge, the actual Cor 3.12 comparison
qThetaPilotLogVolumeComparison C3 P holds.  The bridge itself is not
constructed: its fields are the exact same-C identification, and they are the
only residual in this route.  No carrier, no value-layer surrogate, no sorry.

Normalization caveat (mainline task-13).  The imported comparison
S3131PaperRegionalQ_le_Hull is in the tree's default-residue paperRoot
normalization order(qVFamTensor) / (2l), with the SAME coefficient on both sides.
The paper's Q_p-spectral normalization coefficient is c_norm = order/e;
composing this signed comparison with the spectral normalization needs the
e = 1 / QVFamNormalizedNormCompatibility bridge
(S3131CoefficientReductionActual.S3131PaperRootCoefficient_eq_ramification_mul_rootHalf,
conditional on QVFamNormalizedNormCompatibility).  This file therefore does NOT
claim paper-normalization closure; it is a same-normalization signed comparison.
Mainline reports that the corrected rooted (paper-faithful) comparison is
unconditional at the corrected coefficient paperRoot = e * rootHalf; the only
residual is therefore the coefficient-normalization passage between the paper
Q_p-spectral c_norm = order/e and the tree default-residue order/(2l), i.e.
QVFamNormalizedNormCompatibility / e = 1, not the signed comparison itself.

no axiom.  WRITE-ONLY.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137QThetaComparisonBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S3131QCLeHCComparisonActual
open LeanFormal.IUT.XiFPaper.S3131PaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S3131SameCSourceInputActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
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

/-- **Exact same-C readout bridge (named residual).**  The Stage-2 actual
q-pilot reading and the actual Theta-hull container log-volume of the C3 input
coincide with the Batch A paper-normalized regional readouts of the fixed input
C.  These two equalities are the exact residual same-C identification; they are
not constructed here.  Source: IUT III, Definition 3.8, (i) (p. 112),
Proposition 3.9, (i) (p. 115); Corollary 3.12 (corpus lines 10324--10353). -/
def SameCQThetaReadoutBridge : Prop :=
  qPilotLogVolumeReading P = S3131PaperRegionalQ (l := l) T mu ∧
    thetaPilotHullLogVolumeReal C3 = S3131PaperRegionalHull (l := l) T mu
/-- **Corollary 3.12 on the actual Stage-2 container, reduced to the exact
same-C readout bridge.**  Given the bridge, the actual q-pilot/hull reading
comparison follows from the mainline's unconditional paper-normalized
comparison S3131PaperRegionalQ_le_Hull. -/
theorem qThetaPilotLogVolumeComparison_of_sameC
    (B : SameCQThetaReadoutBridge (l := l) T mu C3 P) :
    qThetaPilotLogVolumeComparison C3 P := by
  obtain ⟨q_eq, h_eq⟩ := B
  unfold qThetaPilotLogVolumeComparison
  rw [q_eq, h_eq]
  exact S3131PaperRegionalQ_le_Hull (l := l) T mu

/-- The magnitude form of the same reduction: given the bridge and the mainline
paper-normalized comparison, the magnitude inequality |log Theta| <= |log q|
holds for the Stage-2 readings. -/
theorem qThetaMagnitudeComparison_of_sameC
    (B : SameCQThetaReadoutBridge (l := l) T mu C3 P) :
    -thetaPilotHullLogVolumeReal C3 <= -qPilotLogVolumeReading P := by
  have hB := qThetaPilotLogVolumeComparison_of_sameC (l := l) T mu C3 P B
  unfold qThetaPilotLogVolumeComparison at hB
  linarith

end LeanFormal.IUT.XiFPaper.S3137QThetaComparisonBridgeActual

namespace LeanFormal.IUT.Audit

/-- **Pending paper-normalization bridge for the q-pilot/Theta-pilot comparison.**
The Stage-2 signed comparison is proved in the tree's default-residue paperRoot
normalization order/(2l) (same coefficient on both sides) from the mainline
unconditional S3131PaperRegionalQ_le_Hull, conditional on the exact same-C
readout bridge.  The paper's Q_p-spectral normalization coefficient is
c_norm = order/e; the e = 1 / QVFamNormalizedNormCompatibility bridge is not
proved here, so paper-normalization closure is not claimed. -/
def qThetaPaperNormalizationBridge : Obligation :=
  { id := "IUT-III.q-theta-paper-normalization-bridge"
    source := "IUT III, Proposition 3.9, (i), p. 115; mainline task-13 coefficient reduction"
    status := VerificationStatus.pending
    note := "Same paperRoot normalization (order/(2l)) comparison only.  Mainline reports the corrected rooted (paper-faithful) comparison UNCONDITIONAL at paperRoot = e * rootHalf; the only residual is the coefficient-normalization passage between the Q_p-spectral c_norm = order/e and the tree default-residue order/(2l), i.e. QVFamNormalizedNormCompatibility / e = 1.  Not proved here; paper-normalization closure not claimed."
    dependsOn := ["S3137QThetaComparisonBridgeActual"] }

end LeanFormal.IUT.Audit