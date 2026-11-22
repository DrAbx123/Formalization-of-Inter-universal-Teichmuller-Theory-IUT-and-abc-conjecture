/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullLogVolumeFormulaActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import Mathlib.Tactic

/-! # CONDITIONAL #7 local ball-log bound (per place) -/

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ExactHullVLocalBoundActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeFormulaActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
structure LocalBallLogBound (b : Bad (nativePlaceSelection T)) where
  bound : Real
  le : (Real.log (rootExtensionHaar T b
      (Metric.closedBall (0 : rootNormedExtension T b)
        ((rootImageRadius T b : NNReal) : Real))).toReal -
      Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal) ≤ bound
theorem localBallLog_le (b : Bad (nativePlaceSelection T))
    (D : LocalBallLogBound (T := T) b) :
    (Real.log (rootExtensionHaar T b
      (Metric.closedBall (0 : rootNormedExtension T b)
        ((rootImageRadius T b : NNReal) : Real))).toReal -
      Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal) ≤ D.bound := D.le
def LocalBallLogBoundRequired (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (LocalBallLogBound (T := T) b)
end LeanFormal.IUT.XiFPaper.Mzk1ExactHullVLocalBoundActual
end