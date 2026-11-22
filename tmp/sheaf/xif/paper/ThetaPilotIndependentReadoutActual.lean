/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual
import tmp.sheaf.xif.paper.GlobalThetaPilotLogVolumeActual
import tmp.sheaf.xif.paper.GlobalQPilotProcessionLogVolumeActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction

/-!
# ThetaPilotIndependentReadoutActual (A497/A498)

Independent Theta-pilot and q/hull readouts, replacing the withdrawn definition
`thetaPilotLogImage = qPilotLogImage/(2l)`:

* `thetaPilotReadout C3 := thetaPilotHullLogVolumeReal C3`: the actual Haar
  log-volume of the actual theta-pilot hull (the C3 tensor log-shell hull region,
  `S3137ThetaHullVolumeScalingActual`, green; equals the actual C3 region by
  `thetaPilotHull_eq_region`);
* `hullReadoutGlobal P := qPilotLogVolumeReading P`: the actual signed q-pilot
  log-volume `-|log q|` on the same C3 input (`S3137QThetaPilotLogVolumeReadingsActual`,
  green), defined independently of theta values;
* `hullReadoutLocal T b := qPilotLogImage T b`: the literal local bad-place signed
  q-log `Real.log ‖(qVFamily T b).q‖` (green double-image asset).

The comparison `hullReadoutGlobal P <= thetaPilotReadout C3` is the real
Step (xi-f) content; it is *not proved* here and is recorded as the named gap
`ThetaHullComparison` (equivalent to the existing named candidate
`qThetaPilotLogVolumeComparison`). No sorry/axiom; no q-derived theta definition.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.ThetaPilotIndependentReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalQPilotProcessionLogVolumeActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.SignedAverageBoundActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open MeasureTheory
open scoped Pointwise ENNReal BigOperators

universe u

/-! ## 1. Independent readouts -/

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}

/-- The Theta-pilot readout: the actual Haar log-volume of the actual theta-pilot
hull (the C3 tensor log-shell hull container). This is a real log-volume on the
actual C3 measure, defined without reference to any q parameter. -/
noncomputable def thetaPilotReadout
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Real :=
  thetaPilotHullLogVolumeReal C3

/-- The q-pilot / hull readout on the actual C3 input: the signed q-pilot
log-volume `-|log q|`, independent of theta values. -/
noncomputable def hullReadoutGlobal
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (l := l) (I := I)) : Real :=
  qPilotLogVolumeReading P

/-- The literal local hull readout at a native bad place: the exact local signed
q-log `Real.log ‖(qVFamily T b).q‖` (negative); this is the bad-place readout used
by the hull lane, independently of any theta value. -/
noncomputable def hullReadoutLocal {T : SourceNativeInitialThetaData.{0} l}
    (b : Bad (nativePlaceSelection T)) : Real :=
  qPilotLogImage T b

/-! ## 2. Elementary facts (proved) -/

theorem thetaPilotReadout_eq_regionLogVolume
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    thetaPilotReadout C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal :=
  LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual.thetaPilotHullLogVolumeReal_eq_actualRegion (C3 := C3)

theorem thetaPilotReadout_eq_hullLogVolume
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    thetaPilotReadout C3 =
      Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal :=
  by
  rw [thetaPilotHull_eq_region]
  exact LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual.thetaPilotHullLogVolumeReal_eq_actualRegion (C3 := C3)

theorem thetaPilotHull_measure_lt_top'
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ :=
  LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual.thetaPilotHull_measure_lt_top (C3 := C3)

theorem hullReadoutGlobal_eq_neg_abs
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    hullReadoutGlobal C3 P = -|Real.log (‖P.line.C3.q.q‖)| :=
  qPilotLogVolumeReading_eq_neg_abs_qParameter P

theorem hullReadoutGlobal_nonpos
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    hullReadoutGlobal C3 P ≤ 0 :=
  qPilotLogVolumeReading_nonpos P

theorem hullReadoutLocal_eq_log_norm {T : SourceNativeInitialThetaData.{0} l}
    (b : Bad (nativePlaceSelection T)) :
    hullReadoutLocal b = Real.log ‖(qVFamily T b).q‖ := rfl

theorem hullReadoutLocal_neg {T : SourceNativeInitialThetaData.{0} l}
    (b : Bad (nativePlaceSelection T)) :
    hullReadoutLocal b < 0 :=
  by
  unfold hullReadoutLocal Mzk1QPilotSHEDoubleImageActual.qPilotLogImage
  exact localSignedLog_neg (qVFamily T b)

/-! ## 3. The Cor 3.12 target statement (A508: target, not a prerequisite)

A508 route analysis: the theta-pilot hull and its log-volume are OBJECTS of the
3.12 route (the hull+det step of 3.11.5; IUT III:10823-10841, 10864-10898).
The inequality below is the conclusion of Cor 3.12 (IUT III:10324-10353,
10888-10898), to be derived from the Theorem 3.11 multiradial route via the
formal Step (xi-f). It is NOT an extra named prerequisite of 3.12; do not assume
it and do not count it as progress on the route. -/

/-- **Cor 3.12 target on one actual C3 input** (the xi-f output statement): the
q-pilot signed log-volume is at most the Theta-pilot hull log-volume. This is the
statement to be derived from the Theorem 3.11/3.11.5 route, not a hypothesis. -/
def cor312ThetaHullComparisonTarget
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (l := l) (I := I)) : Prop :=
  hullReadoutGlobal C3 P ≤ thetaPilotReadout C3

/-! ## 4. The local/global q bridge (named identification) -/

/-- Named identification between the literal double-image q family and the base q
family used by the global q-pilot procession: they have the same completion norm
at every native bad place. This is the source-level clause-B identification; it is
recorded as a hypothesis, not silently assumed. -/
def BaseQNormAgreement {T : SourceNativeInitialThetaData.{0} l} : Prop :=
  ∀ b : Bad (nativePlaceSelection T), ‖(qVFamily T b).q‖ = ‖(baseQ T b).q‖

/-- Under the named base-q agreement, the global q-pilot signed log-volume is the
sum of the local bad-place hull readouts. -/
theorem globalQPilotLogVolume_eq_sum_hullReadoutLocal
    {T : SourceNativeInitialThetaData.{0} l} [Fintype (Bad (nativePlaceSelection T))]
    (h : BaseQNormAgreement (T := T)) :
    globalQPilotLogVolume T = ∑ b : Bad (nativePlaceSelection T), hullReadoutLocal b := by
  unfold globalQPilotLogVolume
  apply Finset.sum_congr rfl
  intro b _
  unfold hullReadoutLocal Mzk1QPilotSHEDoubleImageActual.qPilotLogImage BaseQLogVolumeActual.baseQSignedLog
  unfold localSignedLog
  rw [h b]

/-- Under the named base-q agreement, the global q-pilot log-magnitude is the
negative of the local readout sum. -/
theorem globalQPilotLogMagnitude_eq_neg_sum_hullReadoutLocal
    {T : SourceNativeInitialThetaData.{0} l} [Fintype (Bad (nativePlaceSelection T))]
    (h : BaseQNormAgreement (T := T)) :
    globalQPilotLogMagnitude T = -∑ b : Bad (nativePlaceSelection T), hullReadoutLocal b := by
  unfold globalQPilotLogMagnitude
  rw [globalQPilotLogVolume_eq_sum_hullReadoutLocal h]

/-! ## 5. The rejected q-derived theta candidate (recorded, not used) -/

/-- The raw theta-value procession candidate is the Gauss coefficient times the
global q-pilot log-magnitude. It is a positive raw magnitude on q_v^{j^2}, not the
hull log-volume; it is recorded here only as the rejected normalization. -/
theorem globalThetaPilotLogVolume_formula
    {T : SourceNativeInitialThetaData.{0} l} [Fintype (Bad (nativePlaceSelection T))] :
    globalThetaPilotLogVolume T =
      ((gaussExponentSum (l := l) : Real) /
        (Fintype.card (SignedLabel l.value) : Real)) *
        globalQPilotLogMagnitude T :=
  globalThetaPilotLogVolume_eq (l := l)

end LeanFormal.IUT.XiFPaper.ThetaPilotIndependentReadoutActual
