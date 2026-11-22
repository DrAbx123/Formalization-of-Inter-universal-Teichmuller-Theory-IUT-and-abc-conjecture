/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A1DeltaExplicitActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import Mathlib.Tactic
/-! # weight alignment: nativeBadLocalWeight vs s1915LocalDegree -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0WeightAlignmentActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1A1DeltaExplicitActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open scoped BigOperators
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Weighted local q log sum. -/
noncomputable def a1WeightedQLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight (T := T) b * a1LocalQLog (T := T) (b := b)
/-- Weighted local theta normalized log sum. -/
noncomputable def a1WeightedThetaLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight (T := T) b *
      ((s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real))
/-- Weighted comparison from the actual local q/theta bound and nonnegative weights. -/
theorem a1WeightedQLog_le_thetaLog
    (hd : ∀ b : Bad (nativePlaceSelection T), 0 < s1915LocalDegree T b)
    (hQ0 : ∀ b, rootExtensionHaar T b (c0QLattice T b) ≠ 0)
    (hQtop : ∀ b, rootExtensionHaar T b (c0QLattice T b) ≠ ⊤)
    (hO0 : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hOtop : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤) :
    a1WeightedQLog (T := T) ≤ a1WeightedThetaLog (T := T) := by
  unfold a1WeightedQLog a1WeightedThetaLog
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left
    (a1LocalQLog_le_degree_log_radius (T := T) (b := b) (hd b) (hQ0 b) (hQtop b) (hO0 b) (hOtop b))
    (nativeBadLocalWeight_nonneg T b)
end LeanFormal.IUT.XiFPaper.Mzk1P0WeightAlignmentActual
end