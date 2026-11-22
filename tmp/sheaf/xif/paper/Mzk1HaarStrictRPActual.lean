/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.PaperRootExtensionValuedActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.Mzk1PositiveMeasureQRegionProofActual
import Mathlib.Tactic

/-!
# Mzk1HaarStrictRPActual — general strictly-smaller-radius annulus theorem (A558)

For any positive radius function `r` with `0 < r b < R_b`, the region
`qRegionR = ∏_b closedBall(0, r b)` has positive finite measure, is contained in
the hull, and the hull has STRICTLY larger Haar measure (ultrametric cylinder
argument, radii `r b0 < R_b0`).  This is the corrected radius picture: instantiate
`r b = R_b / p_b` (residue characteristic) to get the genuine `R/p` annulus; the
previous `R/2` can be the same valuation class for odd `p`, which is why this
general statement is needed.

No named strict_measure: strictness is proved by additivity of the product Haar
measure on a positive-measure cylinder disjoint from the region.
No `sorry`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HaarStrictRPActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (r : Bad (nativePlaceSelection T) → Real)
variable (hrpos : ∀ b, 0 < r b)
variable (hrlt : ∀ b, r b < (rootImageRadius T b : Real))

/-- Product region with strictly smaller radii. -/
def qRegionR : Set (S1902Carrier T) :=
  Set.pi Set.univ (fun b => Metric.closedBall (0 : rootNormedExtension T b) (r b))

theorem qRegionR_subset_hull (hrpos : ∀ b, 0 < r b)
    (hrlt : ∀ b, r b < (rootImageRadius T b : Real)) :
    qRegionR T r ⊆ s1902Hull T := by
  intro x hx
  change x ∈ rootExtensionProductImageHull T
  rw [rootExtensionProductImageHull, Set.mem_pi]
  intro b _
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have hxr := hx b (Set.mem_univ b)
  rw [Metric.mem_closedBall, dist_eq_norm] at hxr
  exact le_trans hxr (le_of_lt (hrlt b))

theorem qRegionR_measure_pos (hrpos : ∀ b, 0 < r b) :
    0 < rootExtensionProductHaar T (qRegionR T r) := by
  unfold qRegionR rootExtensionProductHaar
  rw [Measure.pi_pi]
  apply Finset.prod_pos
  intro b _
  exact rootExtensionClosedBall_measure_pos (T := T) (b := b) (r b) (hrpos b)

theorem qRegionR_measure_lt_top : rootExtensionProductHaar T (qRegionR T r) < ⊤ := by
  unfold qRegionR rootExtensionProductHaar
  rw [Measure.pi_pi]
  apply ENNReal.prod_lt_top
  intro b _
  exact rootExtensionClosedBall_measure_lt_top (T := T) (b := b) (r b)

/-- The cylinder at an attaining place and value, with radius `r b0` at `b0`. -/
def annulusCylinderR (b0 : Bad (nativePlaceSelection T))
    (y : rootNormedExtension T b0) : Set (S1902Carrier T) :=
  {x | ‖x b0 - y‖ ≤ r b0 ∧
    ∀ b : Bad (nativePlaceSelection T), b ≠ b0 →
      ‖x b‖ ≤ (rootImageRadius T b : Real)}

theorem annulusCylinderR_subset_hull (hrpos : ∀ b, 0 < r b)
    (hrlt : ∀ b, r b < (rootImageRadius T b : Real))
    (b0 : Bad (nativePlaceSelection T))
    (y : rootNormedExtension T b0)
    (hy : ‖y‖ = (rootImageRadius T b0 : Real)) :
    annulusCylinderR T r b0 y ⊆ s1902Hull T := by
  intro x hx
  change x ∈ rootExtensionProductImageHull T
  rw [rootExtensionProductImageHull, Set.mem_pi]
  intro b hb
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  by_cases hbb : b = b0
  · subst hbb
    have htri : ‖x b0‖ ≤ max ‖x b0 - y‖ ‖y‖ := by
      have hdist := IsUltrametricDist.dist_triangle_max (x b0) y (0 : rootNormedExtension T b0)
      rw [dist_eq_norm, dist_eq_norm, dist_zero_right, sub_zero] at hdist
      exact hdist
    calc ‖x b0‖ ≤ max ‖x b0 - y‖ ‖y‖ := htri
      _ ≤ max (r b0) (rootImageRadius T b0 : Real) := by
          apply max_le_max hx.1 (le_of_eq hy)
      _ = (rootImageRadius T b0 : Real) := by
          apply max_eq_right
          exact le_of_lt (hrlt b0)
  · exact hx.2 b hbb

theorem annulusCylinderR_disjoint_qRegionR (hrpos : ∀ b, 0 < r b)
    (hrlt : ∀ b, r b < (rootImageRadius T b : Real))
    (b0 : Bad (nativePlaceSelection T))
    (y : rootNormedExtension T b0)
    (hy : ‖y‖ = (rootImageRadius T b0 : Real)) :
    Disjoint (annulusCylinderR T r b0 y) (qRegionR T r) := by
  rw [Set.disjoint_left]
  intro x hxC hxQ
  have hx0 : ‖x b0‖ ≤ r b0 := by
    have := hxQ b0 (Set.mem_univ b0)
    simpa [qRegionR, Metric.mem_closedBall, dist_eq_norm] using this
  have htri : ‖y‖ ≤ max ‖x b0 - y‖ ‖x b0‖ := by
    have hdist := IsUltrametricDist.dist_triangle_max y (x b0) (0 : rootNormedExtension T b0)
    rw [dist_eq_norm, dist_eq_norm, dist_zero_right, sub_zero] at hdist
    have hsub : y - x b0 = -(x b0 - y) := by abel
    rw [hsub, norm_neg] at hdist
    exact hdist
  rw [hy] at htri
  have hle : (rootImageRadius T b0 : Real) ≤ r b0 := by
    calc (rootImageRadius T b0 : Real) ≤ max ‖x b0 - y‖ ‖x b0‖ := htri
      _ ≤ max (r b0) (r b0) := max_le_max hxC.1 hx0
      _ = r b0 := max_self _
  linarith [hrlt b0]

end LeanFormal.IUT.XiFPaper.Mzk1HaarStrictRPActual
end
