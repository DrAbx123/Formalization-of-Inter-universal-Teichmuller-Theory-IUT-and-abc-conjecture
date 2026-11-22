/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0RouteC0LogActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open MeasureTheory
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
theorem c0HLattice_subset_unitBall : c0HLattice T b ⊆ c0UnitBall T b := by
  rintro z ⟨y, hy, rfl⟩
  unfold c0UnitBall rootExtensionUnitBall
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_mul]
  have ha : ‖c0Alpha T b‖ ≤ 1 := c0Alpha_norm_le_one T b
  have hy' : ‖y‖ ≤ 1 := by
    simpa [c0UnitBall, rootExtensionUnitBall, Metric.mem_closedBall, dist_eq_norm] using hy
  exact mul_le_one₀ ha (norm_nonneg _) hy'
theorem c0QLattice_measure_le :
    rootExtensionHaar T b (c0QLattice T b) ≤
      rootExtensionHaar T b (c0HLattice T b) :=
  measure_mono (c0QLattice_subset_alpha T b)
theorem c0QLattice_logVolume_le :
    (rootExtensionHaar T b (c0QLattice T b)).toReal ≤
      (rootExtensionHaar T b (c0HLattice T b)).toReal := by
  apply ENNReal.toReal_mono
  · exact ne_of_lt (lt_of_le_of_lt (measure_mono (c0HLattice_subset_unitBall T b))
      (rootExtensionUnitBall_measure_lt_top T b))
  · exact c0QLattice_measure_le T b
end LeanFormal.IUT.XiFPaper.Mzk1P0RouteC0LogActual
end
