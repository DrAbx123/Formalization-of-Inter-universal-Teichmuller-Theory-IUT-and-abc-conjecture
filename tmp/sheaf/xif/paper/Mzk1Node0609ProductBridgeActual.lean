/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P3ProductHaarPiActual
import tmp.sheaf.xif.paper.Mzk1HaarProductStrictMainlineActual
import Mathlib.Tactic
/-! # node06/09 product region bridge to weighted q sum -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Node0609ProductBridgeActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1P3ProductHaarPiActual
open MeasureTheory
open scoped BigOperators ENNReal
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]
/-- The normalized product log of the rpRegion splits into local closed-ball logs. -/
theorem rpRegion_normalizedLog_eq_sum :
    rootExtensionProductNormalizedLog T (rpRegion T) =
      ∑ b : Bad (nativePlaceSelection T),
        (Real.log (rootExtensionHaar T b
            (Metric.closedBall (0 : rootNormedExtension T b) (rpRadius T b))).toReal -
          Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal) := by
  have hS : ∀ b, rootExtensionHaar T b
      (Metric.closedBall (0 : rootNormedExtension T b) (rpRadius T b)) ≠ 0 := by
    intro b
    exact ne_of_gt (rootExtensionClosedBall_measure_pos (T := T) (b := b) _ (rpRadius_pos T b))
  have hSfin : ∀ b, rootExtensionHaar T b
      (Metric.closedBall (0 : rootNormedExtension T b) (rpRadius T b)) ≠ ⊤ := by
    intro b
    exact ne_of_lt (rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _)
  have hU : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0 := by
    intro b; exact ne_of_gt (rootExtensionUnitBall_measure_pos T b)
  have hUfin : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤ := by
    intro b; exact ne_of_lt (rootExtensionUnitBall_measure_lt_top T b)
  simpa [rpRegion] using
    productNormalizedLog_pi T
      (fun b => Metric.closedBall (0 : rootNormedExtension T b) (rpRadius T b))
      hS hSfin hU hUfin
/-- Missing bridge: local closed-ball log sum equals the weighted q sum.
No inhabitant is asserted. -/
def WeightedQSumBridge (localLogSum weightedQSum : ℝ) : Prop := localLogSum = weightedQSum
def bridgeRows : List (String × String) :=
  [ ("rpRegion split", "PROVED: productNormalizedLog = sum local closed-ball logs"),
    ("q weights", "rpRadius = rootImageRadius / qVFamTensorP"),
    ("weighted q sum", "MISSING: local log sum = q weighted sum") ]
theorem bridgeRows_length : bridgeRows.length = 3 := rfl
#check rpRegion_normalizedLog_eq_sum
#check WeightedQSumBridge
end LeanFormal.IUT.XiFPaper.Mzk1Node0609ProductBridgeActual
end