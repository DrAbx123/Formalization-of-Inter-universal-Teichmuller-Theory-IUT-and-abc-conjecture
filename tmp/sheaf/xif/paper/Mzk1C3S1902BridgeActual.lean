/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullLogVolumeFormulaActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import Mathlib.Tactic

/-! # CONDITIONAL C3 ↔ S1902 transport interface

This file defines **named input** `C3S1902TransportData` (no inhabitant is constructed):
a block equivalence, a region equality, a positive Haar scale, and the Haar scaling law.
It then proves the exact formula for the S3137 raw θ read in terms of the S1902 normalized log
plus the explicit normalization correction.

The data is an addressable interface for the reconciliation #5/#2 missing items, **not progress**
and not a proof of `qThetaPilotLogVolumeComparison`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1C3S1902BridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeFormulaActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory
open scoped ENNReal BigOperators

universe u

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Named transport data from the S3137 C3 packet to the S1902 carrier.
These are explicit inputs; no inhabitant is asserted. -/
structure C3S1902TransportData where
  blockEquiv : C3LogShellTensorBlock C3 ≃ S1902Carrier T
  region_eq : blockEquiv '' actualC3LogShellTensorRegion C3 = s1902Hull T
  haarScale : ℝ
  haarScale_pos : 0 < haarScale
  haar_apply : ∀ S : Set (C3LogShellTensorBlock C3),
    (actualC3LogShellTensorHaar C3 S).toReal =
      haarScale * (rootExtensionProductHaar T (blockEquiv '' S)).toReal

theorem hull_measure_toReal_pos :
    0 < (rootExtensionProductHaar T (s1902Hull T)).toReal :=
  ENNReal.toReal_pos (ne_of_gt (PaperRootExtensionThetaHullAuditActual.rootExtensionProductImageHull_measure_pos_lt_top (T := T)).1)
    (ne_of_lt (PaperRootExtensionThetaHullAuditActual.rootExtensionProductImageHull_measure_pos_lt_top (T := T)).2)

theorem unit_measure_toReal_pos :
    0 < (rootExtensionProductHaar T (s1902UnitRegion T)).toReal := by
  rw [s1902UnitRegion]
  exact ENNReal.toReal_pos
    (ne_of_gt (rootExtensionProductHaar_unitBall_pos_lt_top (T := T)).1)
    (ne_of_lt (rootExtensionProductHaar_unitBall_pos_lt_top (T := T)).2)

/-- CONDITIONAL exact formula: the S3137 raw θ read equals the S1902 normalized hull log plus
the explicit normalization correction (Haar scale + S1902 unit mass). -/
theorem thetaRead_eq_s1902_normalized_add_correction
    (D : C3S1902TransportData (T := T) C3) :
    thetaPilotHullLogVolumeReal C3 =
      rootExtensionProductNormalizedLog T (s1902Hull T) +
        (Real.log D.haarScale +
          Real.log (rootExtensionProductHaar T (s1902UnitRegion T)).toReal) := by
  have hH := hull_measure_toReal_pos (T := T)
  have hU := unit_measure_toReal_pos (T := T)
  have hmass := D.haar_apply (actualC3LogShellTensorRegion C3)
  rw [D.region_eq] at hmass
  have hθ : thetaPilotHullLogVolumeReal C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal := by
    unfold thetaPilotHullLogVolumeReal
    rw [S3137QThetaPilotLogVolumeReadingsActual.thetaPilotHull_eq_region]
  rw [hθ, hmass]
  unfold rootExtensionProductNormalizedLog
  rw [Real.log_mul (ne_of_gt D.haarScale_pos) (ne_of_gt hH)]
  simp only [s1902Hull, s1902UnitRegion]
  ring

def C3S1902TransportDataRequired : Prop :=
  Nonempty (C3S1902TransportData (T := T) C3)

def rows : List (String × String × String) :=
  [ ("C3S1902TransportData", "named input: blockEquiv/region_eq/haarScale/haar_apply", "CONDITIONAL (no inhabitant)"),
    ("hull_measure_toReal_pos", "S1902 hull positive", "PROVED"),
    ("thetaRead_eq_s1902_normalized_add_correction", "exact conditional formula", "PROVED"),
    ("qThetaPilotLogVolumeComparison", "not touched", "PENDING") ]

theorem rows_length : rows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1C3S1902BridgeActual

end