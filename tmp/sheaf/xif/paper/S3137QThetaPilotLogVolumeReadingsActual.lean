import tmp.sheaf.xif.paper.QPilotScalarIdentificationActual
import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.S3137LogThetaLatticeLogShellReadyActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import LeanFormal.IUT.Audit.Status

/-!
# S3137: actual q-pilot / Theta-pilot log-volume readings on one C3 input

IUT III, Definition 3.8, (i) (p. 112): the q-pilot object sits at (1,0) and the
Theta-pilot object at (0,0) of the log-theta-lattice; Corollary 3.12, Step
(xi-f), compares -|log(Theta)| with -|log(q)|.  On the same actual C3 source
data this file constructs the two actual readings:

* the q-side reading is the signed log-volume of the actual paper q-pilot
  object P, i.e. P.signedQPilotLogVolume = -|log q| for the actual source
  completion q (production theorem of QPilotScalarIdentificationActual);
* the Theta-side reading is the actual Haar log-volume of the least lambda-O
  holomorphic hull of the actual tensor log-shell region of C3, constructed in
  C3LogShellTensorHolomorphicHullActual; that hull is proved here to be the
  actual region itself, so the reading is the actual container log-volume, and
  its p-scaling is the packet normalization of
  S3137C3LogShellPacketNormalizedLogVolumeActual.

The comparison Q_C <= H_C of the Batch A mainline is stated as the named
candidate Prop qThetaPilotLogVolumeComparison and recorded as a pending Audit
obligation; it is NOT proved here, no carrier is substituted and no value-layer
surrogate is used.  No sorry, no axiom, no True/PUnit.  WRITE-ONLY.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137LogThetaLatticeLogShellReadyActual
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance qThetaBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance qThetaBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-! ## 1. Lattice positions of the two pilots (Definition 3.8, (i)) -/

/-- The q-pilot position (1,0) is the horizontal (1,0)-shift of the Theta-pilot
position (0,0), and (1,1) is the vertical successor of the q-pilot position. -/
theorem pilot_lattice_positions :
    qPilotPosition = horizontalIndex thetaPilotPosition ∧
      comparisonPosition = verticalIndex qPilotPosition := by
  exact ⟨rfl, rfl⟩

/-! ## 2. The actual q-side reading -/

/-- The actual q-pilot log-volume reading: the signed log-volume of the actual
paper q-pilot object. -/
noncomputable def qPilotLogVolumeReading
    (P : PaperQPilotObjectActual (l := l) (I := I)) : ℝ :=
  P.signedQPilotLogVolume

/-- The q-pilot reading is -|log q| for the actual source completion q. -/
theorem qPilotLogVolumeReading_eq_neg_abs_qParameter
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qPilotLogVolumeReading P = -|Real.log (‖P.line.C3.q.q‖)| :=
  signedQPilotLogVolume_eq_neg_abs_qParameter P

/-- The q-pilot reading is nonpositive. -/
theorem qPilotLogVolumeReading_nonpos
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qPilotLogVolumeReading P ≤ 0 :=
  signedQPilotLogVolume_nonpos P

/-! ## 3. The actual Theta-side container and its log-volume reading -/

/-- The actual Theta-side container: the least lambda-O holomorphic hull of the
actual tensor log-shell region of the C3 input. -/
noncomputable def thetaPilotHull : Set (C3LogShellTensorBlock C3) :=
  actualHolomorphicHull C3 (actualUnitRegion C3)

/-- The actual hull container is the actual tensor log-shell region itself: the
region is already a lambda-O region. -/
theorem thetaPilotHull_eq_region :
    thetaPilotHull C3 = actualC3LogShellTensorRegion C3 :=
  actualHolomorphicHull_unitRegion_eq C3

theorem thetaPilotHull_compact : IsCompact (thetaPilotHull C3) := by
  rw [thetaPilotHull_eq_region]
  exact actualC3LogShellTensorRegion_compact C3

/-- The actual Theta-side log-volume reading: the actual Haar log-volume of the
hull container, as an ENNReal (infinite mass kept as top). -/
noncomputable def thetaPilotHullLogVolume : ENNReal :=
  haarLogVolume (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)

theorem thetaPilotHullLogVolume_eq_regionLogVolume :
    thetaPilotHullLogVolume C3 =
      haarLogVolume (actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3) := by
  unfold thetaPilotHullLogVolume
  rw [thetaPilotHull_eq_region]

theorem thetaPilotHullLogVolume_ne_top : thetaPilotHullLogVolume C3 ≠ ⊤ := by
  rw [thetaPilotHullLogVolume_eq_regionLogVolume]
  rw [haarLogVolume_of_lt_top (c3TensorRegion_measure_lt_top (C3 := C3))]
  exact ENNReal.ofReal_ne_top

/-- The real Theta-side log-volume reading. -/
noncomputable def thetaPilotHullLogVolumeReal : ℝ :=
  Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal

theorem thetaPilotHullLogVolumeReal_eq_regionLogVolume :
    thetaPilotHullLogVolumeReal C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal := by
  unfold thetaPilotHullLogVolumeReal
  rw [thetaPilotHull_eq_region]

/-! ## 4. The Batch A comparison candidate (not proved) -/

/-- **Candidate actual q-pilot/Theta-pilot log-volume comparison.**  On the
same actual C3 input, the actual q-pilot log-volume reading is at most the
actual Theta-pilot hull log-volume reading.  This is the Q_C <= H_C comparison
needed by the Batch A mainline (Corollary 3.12, Step (xi-f)); it is a named
candidate, not proved, and no carrier is substituted for its proof. -/
def qThetaPilotLogVolumeComparison
    (P : PaperQPilotObjectActual (l := l) (I := I)) : Prop :=
  qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3

theorem qThetaPilotLogVolumeComparison_iff
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qThetaPilotLogVolumeComparison C3 P ↔
      qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3 := Iff.rfl

end LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual

namespace LeanFormal.IUT.Audit

/-- **Pending actual q-pilot/Theta-pilot log-volume comparison.**  The two
actual readings are constructed on the same C3 input
(S3137QThetaPilotLogVolumeReadingsActual): the q-pilot signed log-volume
P.signedQPilotLogVolume = -|log q| and the actual Theta-pilot hull log-volume
(hull of the actual tensor log-shell region, which equals the region).  The
comparison Q_C <= H_C of Corollary 3.12, Step (xi-f), is not proved. -/
def qThetaPilotLogVolumeComparison : Obligation :=
  { id := "IUT-III.q-pilot-theta-pilot-log-volume-comparison"
    source := "IUT III, Definition 3.8, (i), p. 112; Corollary 3.12, Step (xi-f)"
    status := VerificationStatus.pending
    note := "Actual readings constructed on one C3 input; the inequality between the q-pilot reading and the Theta-pilot hull log-volume reading is the open Batch A comparison.  Not proved; no carrier substituted."
    dependsOn := ["S3137QThetaPilotLogVolumeReadingsActual"] }

end LeanFormal.IUT.Audit