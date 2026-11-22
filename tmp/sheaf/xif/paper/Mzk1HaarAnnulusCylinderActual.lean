/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarStrictActual
import Mathlib.Tactic

/-!
# Mzk1HaarAnnulusCylinderActual — ultrametric annulus cylinder (A552)

The geometric part of the strict Haar increase: at a place `b0` where the hull
radius `R` is attained by a theta value `y` (`||y|| = R > 0`), the cylinder
`C = {x | ||x b0 - y|| ≤ R/4, ||x b|| ≤ R_b for b ≠ b0}` satisfies
* `C ⊆ hull` (ultrametric triangle inequality),
* `C ∩ qRegion = ∅` (otherwise `R = ||y|| ≤ max(R/4,R/2) < R`).
Positivity of `μ C` then feeds `haarStrict_of_positive_annulus`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HaarAnnulusCylinderActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b0 : Bad (nativePlaceSelection T))
variable (y : rootNormedExtension T b0)

/-- The ultrametric annulus cylinder at `(b0, y)`. -/
def annulusCylinder : Set (S1902Carrier T) :=
  {x | ‖x b0 - y‖ ≤ (rootImageRadius T b0 : Real) / 4 ∧
    ∀ b : Bad (nativePlaceSelection T), b ≠ b0 →
      ‖x b‖ ≤ (rootImageRadius T b : Real)}

/-- `C ⊆ hull` when `y` attains the radius `R_b0 > 0`. -/
theorem annulusCylinder_subset_hull
    (hy : ‖y‖ = (rootImageRadius T b0 : Real))
    (hR : 0 < (rootImageRadius T b0 : Real)) :
    annulusCylinder T b0 y ⊆ s1902Hull T := by
  intro x hx
  have hxb := hx.1
  have hxO := hx.2
  intro b hb
  rw [s1902Hull, rootExtensionProductImageHull]
  by_cases hbb : b = b0
  · subst hbb
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have htri : ‖x b0‖ ≤ max ‖x b0 - y‖ ‖y‖ := by
      have hdist := IsUltrametricDist.dist_triangle_max (x b0) y (0 : rootNormedExtension T b0)
      rw [dist_eq_norm, dist_eq_norm, dist_zero_right, sub_zero] at hdist
      exact hdist
    calc ‖x b0‖ ≤ max ‖x b0 - y‖ ‖y‖ := htri
      _ ≤ max ((rootImageRadius T b0 : Real) / 4) (rootImageRadius T b0 : Real) := by
          apply max_le_max hxb (le_of_eq hy)
      _ = (rootImageRadius T b0 : Real) := by
          apply max_eq_right
          linarith
  · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hxO b hbb

/-- `qRegionHalf` and the cylinder are disjoint when `y` attains the radius. -/
theorem annulusCylinder_disjoint_qRegionHalf
    (hy : ‖y‖ = (rootImageRadius T b0 : Real))
    (hR : 0 < (rootImageRadius T b0 : Real)) :
    Disjoint (annulusCylinder T b0 y) (qRegionHalf T) := by
  rw [Set.disjoint_left]
  intro x hxC hxQ
  have hxb := hxC.1
  have hx0 : ‖x b0‖ ≤ (rootImageRadius T b0 : Real) / 2 := by
    have := hxQ b0 (Set.mem_univ b0)
    simpa [qRegionHalf, Metric.mem_closedBall, dist_eq_norm] using this
  have htri : ‖y‖ ≤ max ‖x b0 - y‖ ‖x b0‖ := by
    have hdist := IsUltrametricDist.dist_triangle_max y (x b0) (0 : rootNormedExtension T b0)
    rw [dist_eq_norm, dist_eq_norm, dist_zero_right, sub_zero] at hdist
    have hsub : y - x b0 = -(x b0 - y) := by abel
    rw [hsub, norm_neg] at hdist
    exact hdist
  rw [hy] at htri
  have hle : (rootImageRadius T b0 : Real) ≤ (rootImageRadius T b0 : Real) / 2 := by
    calc (rootImageRadius T b0 : Real) ≤ max ‖x b0 - y‖ ‖x b0‖ := htri
      _ ≤ max ((rootImageRadius T b0 : Real) / 4) ((rootImageRadius T b0 : Real) / 2) := by
          apply max_le_max hxb hx0
      _ = (rootImageRadius T b0 : Real) / 2 := by
          apply max_eq_right
          linarith
  linarith

#check annulusCylinder_subset_hull
#check annulusCylinder_disjoint_qRegionHalf

end LeanFormal.IUT.XiFPaper.Mzk1HaarAnnulusCylinderActual
end
