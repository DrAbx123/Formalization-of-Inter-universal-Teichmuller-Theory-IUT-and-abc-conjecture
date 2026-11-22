/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.Mzk1HullDetStep3115Actual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual

/-! Reuse file: the green hull readout of Mzk1HullDetStep3115Actual
(packetLogVolume/packetDet) tied to the actual C3 Theta-pilot hull log-volume
of S3137. No new axioms/sorry; all declarations are transported from green
assets. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1HullReadoutReuseActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory

universe u

/-! ## 1. The concrete unit packet/state and its readout -/

/-- The multiplicative unit packet on any finite label type. -/
noncomputable def unitPacket (label : Type u) [Fintype label] : PositivePacket label where
  scale := fun _ => 1
  positive := fun _ => one_pos

theorem packetDet_unitPacket (label : Type u) [Fintype label] :
    packetDet (unitPacket label) = 1 := by
  rw [packetDet_eq_prod]
  simp [unitPacket]

/-- A concrete HullDetState with the unit packet and q = 2. -/
noncomputable def unitState (label : Type u) [Fintype label] : HullDetState label where
  packet := unitPacket label
  q := 2
  q_pos := by norm_num
  q_log_ne_zero := by rw [Real.log_ne_zero]; norm_num

/-- The hull readout of the unit state is zero (log of the unit packet). -/
theorem hullReadout_unitState (label : Type u) [Fintype label] :
    hullReadout (unitState label) = 0 := by
  change packetLogVolume (unitPacket label) = 0
  simp [packetLogVolume, unitPacket]

/-- The hull readout is the log of packetDet (green log_eq_log_det). -/
theorem hullReadout_unitState_eq_log_det (label : Type u) [Fintype label] :
    hullReadout (unitState label) = Real.log (packetDet (unitPacket label)) := by
  classical
  rw [hullReadout_eq_log_hullVolume]
  rfl

/-! ## 2. The actual C3 Theta-pilot hull log-volume (S3137) -/

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}

/-- The actual Theta-pilot hull log-volume readout on the C3 input. -/
noncomputable def thetaHullReadout
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Real :=
  thetaPilotHullLogVolumeReal C3

theorem thetaHullReadout_constructed
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    thetaHullReadout C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal :=
  thetaPilotHullLogVolumeReal_eq_actualRegion (C3 := C3)

theorem thetaHullReadout_hull_measure_lt_top
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ :=
  thetaPilotHull_measure_lt_top (C3 := C3)

/-! ## 3. A joint readout package -/

/-- Pair of the finite-packet hull readout and the actual C3 Theta-pilot hull
readout. -/
structure HullReadoutPair (label : Type u) [Fintype label]
    (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  qHullReadout : Real
  qHullReadout_eq : qHullReadout = hullReadout (unitState label)
  thetaHullLogVolume : Real
  thetaHullLogVolume_eq : thetaHullLogVolume = thetaHullReadout C3

noncomputable def hullReadoutPair (label : Type u) [Fintype label]
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    HullReadoutPair label C3 where
  qHullReadout := hullReadout (unitState label)
  qHullReadout_eq := rfl
  thetaHullLogVolume := thetaHullReadout C3
  thetaHullLogVolume_eq := rfl

end LeanFormal.IUT.XiFPaper.Mzk1HullReadoutReuseActual