/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import Mathlib.CategoryTheory.Groupoid
import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual

/-!
# A520 faithful xi-e containment: the actual C3 pilot readings + possible images

**Status: DEFERRED** — downstream `faithfulContract`/call-order edits are incomplete; the file is not gate evidence. The mathematical content (faithful xi-e named input) is unchanged; only the final contract assembly is pending.

Faithful objects (same C3 input, no hcmp/packet surrogate):
* `qPilotLogVolume P = qPilotLogVolumeReading P = P.signedQPilotLogVolume = -|log q|`
  (`S3137QThetaPilotLogVolumeReadingsActual`, negative);
* `thetaPilotHullVolume C3 = thetaPilotHullLogVolumeReal C3`
  `= Real.log (haar C3 (thetaPilotHull C3))`, and `thetaPilotHull = actualRegion`;
* the named candidate `qThetaPilotLogVolumeComparison C3 P` is exactly
  `qPilotLogVolume P <= thetaPilotHullVolume C3` (paper Cor 3.12 comparison).

The Thm 3.11 part is proved: a region contained in the region of a raw-output
representative is contained in the possible images `MRRep.possibleRegion` (green
`MRRep.reg_subset_possibleRegion`).  The only named input is the paper comparison itself,
supplied as the explicit field `containment` of `FaithfulXiEContainment`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1FaithfulXiEContainmentActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open CategoryTheory
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance faithfulBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance faithfulBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-! ## 1. The faithful pilot readings -/

/-- The actual q-pilot log-volume `-|log q|` on the C3 input. -/
def qPilotLogVolume (P : PaperQPilotObjectActual (l := l) (I := I)) : ℝ :=
  qPilotLogVolumeReading P

/-- The q-pilot reading is `-|log q|` of the actual source completion. -/
theorem qPilotLogVolume_eq_neg_abs (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qPilotLogVolume P = -|Real.log (‖P.line.C3.q.q‖)| :=
  qPilotLogVolumeReading_eq_neg_abs_qParameter P

/-- The q-pilot reading is negative (paper: `|log q| > 0`). -/
theorem qPilotLogVolume_neg (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qPilotLogVolume P < 0 := by
  unfold qPilotLogVolume qPilotLogVolumeReading
  exact P.signedQPilotLogVolume_neg

/-- The actual Theta-pilot hull log-volume `-|log(Theta)|`. -/
def thetaPilotHullVolume : ℝ :=
  thetaPilotHullLogVolumeReal C3

/-- The Theta hull reading is the actual Haar log-volume of the actual tensor log-shell
  region (since `thetaPilotHull = actualRegion`). -/
theorem thetaPilotHullVolume_eq_actualRegion :
    thetaPilotHullVolume C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal :=
  thetaPilotHullLogVolumeReal_eq_actualRegion (C3 := C3)

/-- The actual Theta-pilot hull has finite Haar measure. -/
theorem thetaPilotHull_measure_lt_top :
    (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ :=
  S3137ThetaHullVolumeScalingActual.thetaPilotHull_measure_lt_top (C3 := C3)

/-! ## 2. The possible Theta-pilot log-volumes -/

/-- The set `R_{<= -|log(Theta)|}` of possible Theta-pilot log-volumes. -/
def thetaPossibleVolumes : Set ℝ :=
  {mu | mu <= thetaPilotHullVolume C3}

/-- Membership in the possible-volume region is the paper comparison inequality. -/
theorem mem_thetaPossibleVolumes_iff {mu : ℝ} :
    mu ∈ thetaPossibleVolumes C3 ↔ mu <= thetaPilotHullVolume C3 :=
  Iff.rfl

/-! ## 3. Thm 3.11 part: region containment implies possible-image containment -/

open Iut.Multiradial in
/-- **Generic possible-image containment** (Thm 3.11, green `reg_subset_possibleRegion`):
  a region contained in the region of a raw-output representative is contained in the
  possible images of its multiradial representation. -/
theorem possibleRegion_subset {G : Type} [Groupoid G] {A : Type} [Group A]
    (R : Iut.Multiradial.RawOutput G A) {P : G} {X : Type*}
    (reg : R.F.obj P → Set X) (x : R.F.obj P) {qRegion : Set X}
    (hsub : qRegion ⊆ reg x) :
    qRegion ⊆ Iut.Multiradial.MRRep.possibleRegion reg
      (Iut.Multiradial.MRRep.mk (R := R) x) :=
  Set.Subset.trans hsub (Iut.Multiradial.MRRep.reg_subset_possibleRegion reg x)

/-! ## 4. The faithful containment data (minimal named input) -/

/-- **The faithful xi-e containment**: the q-pilot log-volume lies in the possible
  Theta-pilot log-volume region `R_{<= -|log(Theta)|}`.  This is exactly the paper
  comparison (`qThetaPilotLogVolumeComparison`); it is the single explicit named input
  (the multiradial identification of the q-pilot with a possible Theta-pilot output, paper
  Step (xi-e)/(xi-f)); the Thm 3.11 region-containment part is proved above. -/
structure FaithfulXiEContainment
    (P : PaperQPilotObjectActual (l := l) (I := I)) where
  /-- The q-pilot log-volume. -/
  qVolume : ℝ
  /-- The Theta-pilot hull log-volume. -/
  thetaVolume : ℝ
  qVolume_eq : qVolume = qPilotLogVolume P
  thetaVolume_eq : thetaVolume = thetaPilotHullVolume C3
  /-- The paper comparison (named): `-|log q| <= -|log(Theta)|`. -/
  containment : qVolume ∈ thetaPossibleVolumes C3

/-- The containment data from the actual readings, with the comparison as the explicit
  named input. -/
def faithfulXiEContainmentOf (P : PaperQPilotObjectActual (l := l) (I := I))
    (h : qPilotLogVolume P <= thetaPilotHullVolume C3) :
    FaithfulXiEContainment C3 P where
  qVolume := qPilotLogVolume P
  thetaVolume := thetaPilotHullVolume C3
  qVolume_eq := rfl
  thetaVolume_eq := rfl
  containment := h

/-- The containment is equivalent to the named candidate `qThetaPilotLogVolumeComparison`
  (same comparison, no surrogate). -/
theorem faithfulContainment_iff_comparison
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qThetaPilotLogVolumeComparison C3 P ↔
      qPilotLogVolume P ∈ thetaPossibleVolumes C3 := by
  unfold qThetaPilotLogVolumeComparison thetaPossibleVolumes qPilotLogVolume
    thetaPilotHullVolume qPilotLogVolumeReading
  exact Iff.rfl

/-- The containment as the paper inequality. -/
theorem faithful_inequality (D : FaithfulXiEContainment C3 P) :
    D.qVolume <= D.thetaVolume := by
  rw [D.qVolume_eq, D.thetaVolume_eq]
  simpa [thetaPossibleVolumes, D.qVolume_eq] using D.containment

/-- The StepXI contract from the faithful containment: `qSigned = -|log q|`,
  `thetaSigned = -|log(Theta)|`, with the xi-f ordering PROVED from the containment. -/
def faithfulContract (D : FaithfulXiEContainment C3 P) (ipl she apt : Prop)
    (hipl : ipl) (hshe : she) (hapt : apt) : StepXIContract where
  qSigned := D.qVolume
  thetaSigned := D.thetaVolume
  targetSigned := D.qVolume
  q_negative := by
    rw [D.qVolume_eq]
    exact qPilotLogVolume_neg P
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := hipl
  she_evidence := hshe
  apt_evidence := hapt
  q_le_target := le_rfl
  target_le_theta := by
    rw [D.qVolume_eq, D.thetaVolume_eq]
    simpa [thetaPossibleVolumes, D.qVolume_eq] using D.containment

/-- Cor 3.12 ordered conclusion from the faithful containment. -/
theorem cor312Conclusion_of_faithful (D : FaithfulXiEContainment C3 P)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ({ qSigned := D.qVolume
        thetaSigned := D.thetaVolume
        targetSigned := D.qVolume
        q_negative := by
          rw [D.qVolume_eq]
          exact qPilotLogVolume_neg P
        ipl := ipl
        she := she
        apt := apt
        ipl_evidence := hipl
        she_evidence := hshe
        apt_evidence := hapt
        q_le_target := le_rfl
        target_le_theta := by
          rw [D.qVolume_eq, D.thetaVolume_eq]
          simpa [thetaPossibleVolumes, D.qVolume_eq] using D.containment } : StepXIContract) :=
  cor312_of_constructed_stepXI _

end LeanFormal.IUT.XiFPaper.Mzk1FaithfulXiEContainmentActual