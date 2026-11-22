/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullUBLocalThirdActual
import tmp.sheaf.xif.paper.Mzk1HaarCylinderMeasureActual
import tmp.sheaf.xif.paper.Mzk1HaarStrictActual
import Mathlib.Tactic
/-! # A6: local three-translate Haar bound 3*mu(H) <= mu(unitBall) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HullUBLocalThirdBoundActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarCylinderMeasureActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictActual
open MeasureTheory
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
theorem local_third_mul_le
    (hultra : IsUltrametricDist (rootNormedExtension T b))
    (hr : (rootImageRadius T b : Real) < 1) :
    (3 : ENNReal) * rootExtensionHaar T b
        (Metric.closedBall (0 : rootNormedExtension T b) (rootImageRadius T b : Real)) ≤
      rootExtensionHaar T b (rootExtensionUnitBall T b) := by
  letI : IsUltrametricDist (rootNormedExtension T b) := hultra
  let r : Real := (rootImageRadius T b : Real)
  let H0 : Set (rootNormedExtension T b) := Metric.closedBall 0 r
  let H1 : Set (rootNormedExtension T b) := Metric.closedBall 1 r
  let H2 : Set (rootNormedExtension T b) := Metric.closedBall 2 r
  let O : Set (rootNormedExtension T b) := rootExtensionUnitBall T b
  have hO : O = Metric.closedBall (0 : rootNormedExtension T b) 1 := rfl
  have hm0 : MeasurableSet H0 := measurableSet_closedBall
  have hm1 : MeasurableSet H1 := measurableSet_closedBall
  have hm2 : MeasurableSet H2 := measurableSet_closedBall
  have hnot01 : (1 : rootNormedExtension T b) ∉ H0 := by
    rw [H0, Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖(1 : rootNormedExtension T b)‖ = 1 := norm_one
    rw [h1]; linarith
  have hnot21 : (2 : rootNormedExtension T b) ∉ H0 := by
    rw [H0, Metric.mem_closedBall, dist_zero_right]
    have h2 : ‖(2 : rootNormedExtension T b)‖ ≤ 1 :=
      IsUltrametricDist.norm_natCast_le_one _ 2
    linarith
  have hnot12 : (2 : rootNormedExtension T b) ∉ H1 := by
    rw [H1, Metric.mem_closedBall]
    have hd : dist (2 : rootNormedExtension T b) 1 = 1 := by
      rw [dist_eq_norm]
      have : (2 : rootNormedExtension T b) - 1 = 1 := by norm_num
      rw [this, norm_one]
    rw [hd]; linarith
  have hd01 : Disjoint H0 H1 := closedBall_disjoint_of_not_mem hnot01
  have hd02 : Disjoint H0 H2 := closedBall_disjoint_of_not_mem hnot21
  have hd12 : Disjoint H1 H2 := closedBall_disjoint_of_not_mem hnot12
  have hd012 : Disjoint (H0 ∪ H1) H2 := by
    rw [Set.disjoint_left]
    intro x hx hx2
    rcases hx with hx0 | hx1
    · exact Set.disjoint_left.mp hd02 hx0 hx2
    · exact Set.disjoint_left.mp hd12 hx1 hx2
  have hsub0 : H0 ⊆ O := by
    rw [H0, hO]
    exact Metric.closedBall_subset_closedBall (le_of_lt hr)
  have hsub1 : H1 ⊆ O := by
    rw [H1, hO]
    intro x hx
    rw [Metric.mem_closedBall] at hx ⊢
    calc dist x 0 ≤ max (dist x 1) (dist 1 0) := dist_triangle_max x 1 0
      _ ≤ 1 := by
        apply max_le hx
        simp
  have hsub2 : H2 ⊆ O := by
    rw [H2, hO]
    intro x hx
    rw [Metric.mem_closedBall] at hx ⊢
    calc dist x 0 ≤ max (dist x 2) (dist 2 0) := dist_triangle_max x 2 0
      _ ≤ 1 := by
        apply max_le hx
        rw [dist_eq_norm]
        exact IsUltrametricDist.norm_natCast_le_one _ 2
  have hsub : H0 ∪ H1 ∪ H2 ⊆ O := by
    intro x hx
    rcases hx with (hx | hx) | hx
    · exact hsub0 hx
    · exact hsub1 hx
    · exact hsub2 hx
  have hmu1 : rootExtensionHaar T b H1 = rootExtensionHaar T b H0 := by
    rw [H1, H0]
    exact rootExtensionHaar_closedBall_translate T b 1 r
  have hmu2 : rootExtensionHaar T b H2 = rootExtensionHaar T b H0 := by
    rw [H2, H0]
    exact rootExtensionHaar_closedBall_translate T b 2 r
  have hu1 : rootExtensionHaar T b (H0 ∪ H1) =
      rootExtensionHaar T b H0 + rootExtensionHaar T b H1 :=
    measure_union hd01 hm0 hm1
  have hu2 : rootExtensionHaar T b ((H0 ∪ H1) ∪ H2) =
      rootExtensionHaar T b (H0 ∪ H1) + rootExtensionHaar T b H2 :=
    measure_union hd012 (hm0.union hm1) hm2
  calc
    (3 : ENNReal) * rootExtensionHaar T b H0 =
        rootExtensionHaar T b H0 + rootExtensionHaar T b H0 + rootExtensionHaar T b H0 := by ring
    _ = rootExtensionHaar T b H0 + rootExtensionHaar T b H1 + rootExtensionHaar T b H2 := by
      rw [hmu1, hmu2]
    _ = rootExtensionHaar T b (H0 ∪ H1) + rootExtensionHaar T b H2 := by rw [hu1]
    _ = rootExtensionHaar T b ((H0 ∪ H1) ∪ H2) := by rw [hu2]
    _ ≤ rootExtensionHaar T b O := measure_mono hsub
    _ = rootExtensionHaar T b (rootExtensionUnitBall T b) := rfl
end LeanFormal.IUT.XiFPaper.Mzk1HullUBLocalThirdBoundActual
end
