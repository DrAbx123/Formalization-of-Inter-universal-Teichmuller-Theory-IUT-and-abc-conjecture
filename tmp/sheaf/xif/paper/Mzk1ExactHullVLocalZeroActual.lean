/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullLogVolumeFormulaActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import Mathlib.Tactic
/-! # #7 actual local bound: ball log minus unit log <= 0 -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ExactHullVLocalZeroActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem localBallLog_sub_unit_le_zero (b : Bad (nativePlaceSelection T)) :
    (Real.log (rootExtensionHaar T b
      (Metric.closedBall (0 : rootNormedExtension T b)
        ((rootImageRadius T b : NNReal) : Real))).toReal -
      Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal) ≤ 0 := by
  have hR : (rootImageRadius T b : Real) ≤ 1 := s1915_rootImageRadius_le_one T b
  have hsub : Metric.closedBall (0 : rootNormedExtension T b)
      ((rootImageRadius T b : NNReal) : Real) ⊆ rootExtensionUnitBall T b := by
    unfold rootExtensionUnitBall
    exact Metric.closedBall_subset_closedBall hR
  have hBpos : 0 < rootExtensionHaar T b
      (Metric.closedBall (0 : rootNormedExtension T b)
        ((rootImageRadius T b : NNReal) : Real)) :=
    rootExtensionClosedBall_measure_pos (T := T) (b := b)
      ((rootImageRadius T b : NNReal) : Real)
      (by exact_mod_cast rootImageRadius_pos (T := T) (b := b))
  have hUpos : 0 < rootExtensionHaar T b (rootExtensionUnitBall T b) :=
    rootExtensionUnitBall_measure_pos T b
  have hle : rootExtensionHaar T b
      (Metric.closedBall (0 : rootNormedExtension T b)
        ((rootImageRadius T b : NNReal) : Real)) ≤
      rootExtensionHaar T b (rootExtensionUnitBall T b) := measure_mono hsub
  have hleR : (rootExtensionHaar T b
      (Metric.closedBall (0 : rootNormedExtension T b)
        ((rootImageRadius T b : NNReal) : Real))).toReal ≤
      (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal :=
    ENNReal.toReal_mono (ne_of_lt (rootExtensionClosedBall_measure_lt_top (T := T) (b := b) 1)) hle
  have hBposR : 0 < (rootExtensionHaar T b
      (Metric.closedBall (0 : rootNormedExtension T b)
        ((rootImageRadius T b : NNReal) : Real))).toReal :=
    ENNReal.toReal_pos (ne_of_gt hBpos)
      (ne_of_lt (rootExtensionClosedBall_measure_lt_top (T := T) (b := b)
        ((rootImageRadius T b : NNReal) : Real)))
  have hlog := Real.log_le_log hBposR hleR
  linarith
end LeanFormal.IUT.XiFPaper.Mzk1ExactHullVLocalZeroActual
end