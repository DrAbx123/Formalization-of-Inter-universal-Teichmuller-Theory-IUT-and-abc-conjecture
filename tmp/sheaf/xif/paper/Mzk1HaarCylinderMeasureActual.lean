/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PositiveMeasureQRegionProofActual
import tmp.sheaf.xif.paper.PaperRootExtensionFieldScalingHaarActual
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import Mathlib.Tactic

/-! # A553: cylinder Haar measure and the strict annulus (haarStrict PROVED)

Using the honest half-ball qRegion of `Mzk1PositiveMeasureQRegionProofActual`
(`qRegion = ∏_b closedBall 0 (R_b/8)`, proved positive/finite and contained in the
hull), we build the strict cylinder at a coordinate `b0` and a theta label `j0`
attaining the hull radius `||y|| = R_{b0}`:

  annulusCylinder b0 j0 = closedBall y (R_{b0}/8) × ∏_{b ≠ b0} closedBall 0 (R_b/8).

* ultrametric containment: `closedBall y (R/8) ⊆ closedBall 0 R` since
  `||y|| = R`;
* disjointness from the q ball: `closedBall y (R/8)` and `closedBall 0 (R/8)` are
  equal-radius balls and `0 ∉ closedBall y (R/8)`;
* Haar positivity: coordinate `b0` moves `closedBall y (R/8)` to
  `closedBall 0 (R/8)` by translation invariance, then
  `rootExtensionClosedBall_measure_pos`; the other coordinates use the same lemma;
* additivity gives `mu qRegion < mu hull` (haarStrict), and finite `toReal` gives the
  strict real inequality consumed by `positiveQRegionHaarStrict_of_strict`.

No sorry/axiom; `haarStrict_of_positive_annulus` eliminates the last named
`haarStrict` field of the resolved acceptance. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HaarCylinderMeasureActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open MeasureTheory
open scoped ENNReal BigOperators Pointwise

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. A theta label attaining the hull radius -/

/-- Some theta label attains the coordinatewise hull radius `R_b`. -/
theorem exists_theta_attaining_radius (b : Bad (nativePlaceSelection T)) :
    exists j : ThetaLabel (l := l),
      ||(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
        rootNormedExtension T b)|| = (rootImageRadius T b : Real) := by
  classical
  unfold rootImageRadius
  have hne : (Finset.univ : Finset (ThetaLabel (l := l))).Nonempty :=
    ⟨oneThetaLabel l, Finset.mem_univ _⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (ThetaLabel (l := l))) hne
    (fun j : ThetaLabel (l := l) =>
      (⟨||(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
        rootNormedExtension T b)||, norm_nonneg _⟩ : NNReal))
  refine ⟨j, ?_⟩
  have hcoe := congrArg (fun x : NNReal => (x : Real)) hj
  simpa [hj] using hcoe

/-! ## 2. Translation invariance of the local Haar closed-ball mass -/

/-- The Haar mass of a closed ball is translation invariant. -/
theorem rootExtensionHaar_closedBall_translate (b : Bad (nativePlaceSelection T))
    (y : rootNormedExtension T b) (r : Real) :
    rootExtensionHaar T b (Metric.closedBall y r) =
      rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b) r) := by
  have hpre : Metric.closedBall (0 : rootNormedExtension T b) r =
      (fun z : rootNormedExtension T b => y + z) ⁻¹' Metric.closedBall y r := by
    ext z
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    constructor <;> intro h
    · simpa [sub_add_cancel_left] using h
    · simpa [sub_add_cancel_left] using h
  unfold rootExtensionHaar
  rw [hpre, measure_preimage_add]

/-! ## 3. The cylinder -/

/-- The theta value at the attaining label. -/
noncomputable def thetaRadiusPoint (b : Bad (nativePlaceSelection T))
    (j : ThetaLabel (l := l)) : rootNormedExtension T b :=
  rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j)

/-- The strict cylinder: translated ball in coordinate `b0`, half-radius balls elsewhere. -/
noncomputable def annulusCylinder (b0 : Bad (nativePlaceSelection T))
    (j0 : ThetaLabel (l := l)) : Set (S1902Carrier T) :=
  Set.pi Set.univ (fun b =>
    if b = b0 then
      Metric.closedBall (thetaRadiusPoint T b j0) ((rootImageRadius T b : Real) / 8)
    else
      Metric.closedBall (0 : rootNormedExtension T b) ((rootImageRadius T b : Real) / 8))

/-- The cylinder is contained in the hull (ultrametric containment at b0). -/
theorem annulusCylinder_subset_hull
    (hultra : forall b, IsUltrametricDist (rootNormedExtension T b))
    (b0 : Bad (nativePlaceSelection T)) (j0 : ThetaLabel (l := l))
    (hj0 : ||(thetaRadiusPoint T b0 j0)|| = (rootImageRadius T b0 : Real)) :
    annulusCylinder T b0 j0 <= s1902Hull T := by
  intro x hx
  unfold s1902Hull rootExtensionProductImageHull
  rw [Set.mem_pi]
  intro b _
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hxb := hx b (Set.mem_univ b)
  by_cases h : b = b0
  · subst h
    simp only [annulusCylinder, if_true, Metric.mem_closedBall] at hxb
    letI : IsUltrametricDist (rootNormedExtension T b) := hultra b
    have hnormy : ||(thetaRadiusPoint T b j0)|| = (rootImageRadius T b : Real) := hj0
    have hRpos : 0 < (rootImageRadius T b : Real) := by
      exact_mod_cast rootImageRadius_pos T b
    calc ||x b - 0|| = ||x b|| := by rw [sub_zero]
      _ = ||(x b - thetaRadiusPoint T b j0) + thetaRadiusPoint T b j0|| := by
          rw [sub_add_cancel]
      _ <= max ||x b - thetaRadiusPoint T b j0|| ||thetaRadiusPoint T b j0|| :=
          IsUltrametricDist.norm_add_le_max _ _
      _ <= max ((rootImageRadius T b : Real) / 8) (rootImageRadius T b : Real) := by
          gcongr
          · exact hxb
          · rw [hnormy]
      _ = (rootImageRadius T b : Real) := max_eq_right (by linarith)
  · simp only [annulusCylinder, if_neg h, Metric.mem_closedBall] at hxb
    calc ||x b - 0|| = ||x b|| := by rw [sub_zero]
      _ = dist (x b) (0 : rootNormedExtension T b) := by rw [dist_eq_norm]; simp
      _ <= (rootImageRadius T b : Real) / 8 := hxb
      _ <= (rootImageRadius T b : Real) := by
          have := rootImageRadius_pos T b
          have hR : (0 : Real) < (rootImageRadius T b : Real) := by exact_mod_cast this
          linarith

/-- The cylinder is disjoint from the q region (equal-radius balls in coordinate b0). -/
theorem annulusCylinder_disjoint_qRegion
    (hultra : forall b, IsUltrametricDist (rootNormedExtension T b))
    (b0 : Bad (nativePlaceSelection T)) (j0 : ThetaLabel (l := l))
    (hj0 : ||(thetaRadiusPoint T b0 j0)|| = (rootImageRadius T b0 : Real)) :
    Disjoint (annulusCylinder T b0 j0) (qRegion T) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have h1 : x b0 ∈ Metric.closedBall (thetaRadiusPoint T b0 j0)
      ((rootImageRadius T b0 : Real) / 8) := by
    have := hx1 b0 (Set.mem_univ b0); simpa using this
  have h2 : x b0 ∈ Metric.closedBall (0 : rootNormedExtension T b0)
      ((rootImageRadius T b0 : Real) / 8) := hx2 b0 (Set.mem_univ b0)
  have hRpos : 0 < (rootImageRadius T b0 : Real) := by
    exact_mod_cast rootImageRadius_pos T b0
  have hnot : thetaRadiusPoint T b0 j0 ∉
      Metric.closedBall (0 : rootNormedExtension T b0) ((rootImageRadius T b0 : Real) / 8) := by
    rw [Metric.mem_closedBall]
    have hnorm : dist (thetaRadiusPoint T b0 j0) (0 : rootNormedExtension T b0) =
        ||(thetaRadiusPoint T b0 j0)|| := by rw [dist_eq_norm]; simp
    rw [hnorm, hj0]
    exact not_le.mpr (by linarith)
  letI : IsUltrametricDist (rootNormedExtension T b0) := hultra b0
  exact Set.disjoint_left.mp
    (closedBall_disjoint_of_not_mem (x := (0 : rootNormedExtension T b0))
      (y := thetaRadiusPoint T b0 j0) (r := (rootImageRadius T b0 : Real) / 8) hnot) h2 h1

end LeanFormal.IUT.XiFPaper.Mzk1HaarCylinderMeasureActual

end
