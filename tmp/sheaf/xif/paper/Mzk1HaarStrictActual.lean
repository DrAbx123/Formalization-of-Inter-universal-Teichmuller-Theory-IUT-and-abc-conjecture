/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.PaperRootExtensionNormBoundActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import Mathlib.Tactic

/-! # A552: strict Haar increase via ultrametric disjointness (haarStrict)

The ball-annulus in a nonarchimedean field can have POSITIVE measure: inside the
hull ball `closedBall 0 R` there is a ball `closedBall 0 s` with `0 < s < R` and a
transported q-ball `closedBall q t` with `t < ||q||`, so the two equal-radius balls
`closedBall 0 s` and `closedBall q s` are disjoint (ultrametric: intersecting
equal-radius balls coincide, but `q` is not in `closedBall 0 s`).

For the product hull `Set.pi univ (fun b => closedBall 0 (R b))` we therefore get a
cylinder `C = closedBall 0 s × ∏_{b≠b0} closedBall 0 (R b)` which is

* contained in the hull,
* disjoint from the positive-measure q region,
* of positive finite product Haar measure (product of closed-ball masses),

so additivity gives `mu qRegion < mu hull` STRICTLY.  This proves `haarStrict`
(the former named `strict_measure`) for the positive-measure q region; the only
extra geometric inputs are the paper p-adic ultrametric structure
(`hultra : forall b, IsUltrametricDist (rootNormedExtension T b)`) and the standard
nonvanishing `0 < ||q||`, `||q|| < R`.

All arguments are true theorems; no sorry/axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HaarStrictActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionNormBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open MeasureTheory
open scoped ENNReal BigOperators Pointwise

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. Ultrametric ball disjointness -/

/-- In an ultrametric space, two closed balls of the same radius are disjoint when
one centre is not in the other ball. -/
theorem closedBall_disjoint_of_not_mem {E : Type*} [PseudoMetricSpace E]
    [IsUltrametricDist E] {x y : E} {r : Real}
    (h : y ∉ Metric.closedBall x r) :
    Disjoint (Metric.closedBall x r) (Metric.closedBall y r) := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  rw [Metric.mem_closedBall] at hz1 hz2 h
  have hxy : dist x y <= r := by
    calc dist x y = dist y x := dist_comm _ _
      _ <= max (dist y z) (dist z x) := dist_triangle_max y z x
      _ <= r := by
        apply max_le
        · simpa [dist_comm] using hz2
        · simpa [dist_comm] using hz1
  exact h hxy

/-- In an ultrametric space, if `dist x y <= r` and `dist y z <= r` then
`dist x z <= r` (the ball is closed under the ultrametric triangle). -/
theorem closedBall_trans {E : Type*} [PseudoMetricSpace E] [IsUltrametricDist E]
    {x y z : E} {r : Real} (hxy : dist x y <= r) (hyz : dist y z <= r) :
    dist x z <= r := by
  calc dist x z <= max (dist x y) (dist y z) := dist_triangle_max x y z
    _ <= r := max_le hxy hyz

/-! ## 2. The refined positive-measure q ball and the strict cylinder -/

/-- Refined q-ball radius: at most half the hull margin and at most half the q norm,
so the ball is disjoint from the zero ball of the same radius. -/
noncomputable def qFitRadius (b : Bad (nativePlaceSelection T)) : Real :=
  min ((rootImageRadius T b - ‖qPilotInThetaCarrier T b‖) / 2)
    (‖qPilotInThetaCarrier T b‖ / 2)

theorem qFitRadius_pos (hstrict : forall b : Bad (nativePlaceSelection T),
      ‖qPilotInThetaCarrier T b‖ < (rootImageRadius T b : Real))
    (hqpos : forall b : Bad (nativePlaceSelection T),
      0 < ‖qPilotInThetaCarrier T b‖) (b : Bad (nativePlaceSelection T)) :
    0 < qFitRadius T b := by
  unfold qFitRadius
  have h1 := hstrict b
  have h2 := hqpos b
  apply lt_min
  · nlinarith
  · nlinarith

theorem qFitRadius_lt_norm (hqpos : forall b : Bad (nativePlaceSelection T),
      0 < ‖qPilotInThetaCarrier T b‖) (b : Bad (nativePlaceSelection T)) :
    qFitRadius T b < ‖qPilotInThetaCarrier T b‖ := by
  unfold qFitRadius
  have h := min_le_right ((rootImageRadius T b - ‖qPilotInThetaCarrier T b‖) / 2)
    (‖qPilotInThetaCarrier T b‖ / 2)
  have h2 := hqpos b
  linarith

theorem qFitRadius_le_margin (hstrict : forall b : Bad (nativePlaceSelection T),
      ‖qPilotInThetaCarrier T b‖ < (rootImageRadius T b : Real))
    (hqpos : forall b : Bad (nativePlaceSelection T),
      0 < ‖qPilotInThetaCarrier T b‖) (b : Bad (nativePlaceSelection T)) :
    qFitRadius T b <= (rootImageRadius T b - ‖qPilotInThetaCarrier T b‖) / 2 :=
  min_le_left _ _

theorem qFitRadius_le_radius (b : Bad (nativePlaceSelection T)) :
    qFitRadius T b <= (rootImageRadius T b : Real) := by
  unfold qFitRadius
  have hq := norm_nonneg (qPilotInThetaCarrier T b)
  have hR := rootImageRadius_pos (T := T) (b := b)
  have h1 : (rootImageRadius T b - ‖qPilotInThetaCarrier T b‖) / 2 <=
      (rootImageRadius T b : Real) := by nlinarith
  have h2 : ‖qPilotInThetaCarrier T b‖ / 2 <= (rootImageRadius T b : Real) := by
    nlinarith [hR]
  exact le_trans (min_le_left _ _) h1

/-- The refined positive-measure q region. -/
noncomputable def qBallRegion : Set (S1902Carrier T) :=
  Set.pi Set.univ (fun b => Metric.closedBall (qPilotInThetaCarrier T b) (qFitRadius T b))

/-- The strict cylinder inside the hull, disjoint from the q ball in coordinate b0. -/
noncomputable def strictCylinder (b0 : Bad (nativePlaceSelection T)) :
    Set (S1902Carrier T) :=
  Set.pi Set.univ (fun b =>
    if b = b0 then Metric.closedBall (0 : rootNormedExtension T b) (qFitRadius T b0)
    else Metric.closedBall (0 : rootNormedExtension T b) (rootImageRadius T b))

/-- The q ball lies in the actual hull (refined radius version). -/
theorem qBallRegion_subset_hull (hstrict : forall b : Bad (nativePlaceSelection T),
      ‖qPilotInThetaCarrier T b‖ < (rootImageRadius T b : Real))
    (hqpos : forall b : Bad (nativePlaceSelection T),
      0 < ‖qPilotInThetaCarrier T b‖) :
    qBallRegion T <= s1902Hull T := by
  intro x hx
  unfold s1902Hull rootExtensionProductImageHull
  rw [Set.mem_pi]
  intro b _
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hxb : x b ∈ Metric.closedBall (qPilotInThetaCarrier T b) (qFitRadius T b) :=
    hx b (Set.mem_univ b)
  rw [Metric.mem_closedBall] at hxb
  have hxb_norm : ‖x b - qPilotInThetaCarrier T b‖ <= qFitRadius T b := by
    rw [← dist_eq_norm]; exact hxb
  calc ‖x b - 0‖ = ‖(x b - qPilotInThetaCarrier T b) +
        qPilotInThetaCarrier T b‖ := by rw [sub_add_cancel]
    _ <= ‖x b - qPilotInThetaCarrier T b‖ + ‖qPilotInThetaCarrier T b‖ := norm_add_le _ _
    _ <= qFitRadius T b + ‖qPilotInThetaCarrier T b‖ := add_le_add_right hxb_norm _
    _ <= (rootImageRadius T b - ‖qPilotInThetaCarrier T b‖) / 2 +
        ‖qPilotInThetaCarrier T b‖ := by
        have := qFitRadius_le_margin T hstrict hqpos b
        nlinarith
    _ < (rootImageRadius T b : Real) := by
        have := hstrict b; nlinarith

/-- The strict cylinder lies in the hull. -/
theorem strictCylinder_subset_hull (hstrict : forall b : Bad (nativePlaceSelection T),
      ‖qPilotInThetaCarrier T b‖ < (rootImageRadius T b : Real))
    (hqpos : forall b : Bad (nativePlaceSelection T),
      0 < ‖qPilotInThetaCarrier T b‖)
    (hultra : forall b, IsUltrametricDist (rootNormedExtension T b))
    (b0 : Bad (nativePlaceSelection T)) :
    strictCylinder T b0 <= s1902Hull T := by
  intro x hx
  unfold s1902Hull rootExtensionProductImageHull
  rw [Set.mem_pi]
  intro b _
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hxb : x b ∈ (if b = b0 then
      Metric.closedBall (0 : rootNormedExtension T b) (qFitRadius T b0)
      else Metric.closedBall (0 : rootNormedExtension T b) (rootImageRadius T b)) :=
    hx b (Set.mem_univ b)
  by_cases h : b = b0
  · subst h
    simp only [if_true, Metric.mem_closedBall] at hxb
    have hle := qFitRadius_le_radius T b
    calc ‖x b - 0‖ = dist (x b) 0 := by rw [dist_eq_norm]
      _ <= qFitRadius T b := hxb
      _ <= (rootImageRadius T b : Real) := hle
  · simp only [if_neg h, Metric.mem_closedBall] at hxb
    calc ‖x b - 0‖ = dist (x b) 0 := by rw [dist_eq_norm]
      _ <= (rootImageRadius T b : Real) := hxb

/-- The cylinder is disjoint from the q ball (the coordinate b0 balls are disjoint). -/
theorem strictCylinder_disjoint_qBall (hqpos : forall b : Bad (nativePlaceSelection T),
      0 < ‖qPilotInThetaCarrier T b‖)
    (hultra : forall b, IsUltrametricDist (rootNormedExtension T b))
    (b0 : Bad (nativePlaceSelection T)) :
    Disjoint (strictCylinder T b0) (qBallRegion T) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have h1 : x b0 ∈ Metric.closedBall (0 : rootNormedExtension T b0) (qFitRadius T b0) := by
    have := hx1 b0 (Set.mem_univ b0)
    simpa using this
  have h2 : x b0 ∈ Metric.closedBall (qPilotInThetaCarrier T b0)
      (qFitRadius T b0) := hx2 b0 (Set.mem_univ b0)
  have hnot : qPilotInThetaCarrier T b0 ∉
      Metric.closedBall (0 : rootNormedExtension T b0) (qFitRadius T b0) := by
    rw [Metric.mem_closedBall]
    have hlt := qFitRadius_lt_norm T hqpos b0
    have hnorm : dist (qPilotInThetaCarrier T b0) (0 : rootNormedExtension T b0) =
        ‖qPilotInThetaCarrier T b0‖ := by rw [dist_eq_norm]; simp
    rw [hnorm]
    exact not_le.mpr hlt
  letI : IsUltrametricDist (rootNormedExtension T b0) := hultra b0
  have hdisj := closedBall_disjoint_of_not_mem (x := (0 : rootNormedExtension T b0))
    (y := qPilotInThetaCarrier T b0) (r := qFitRadius T b0) hnot
  exact Set.disjoint_left.mp hdisj h1 h2


/-! ## 3. Product Haar strict increase (haarStrict) -/

theorem rootExtensionHaar_closedBall_zero_pos (b : Bad (nativePlaceSelection T)) :
    0 < rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
      (rootImageRadius T b : Real)) := by
  unfold rootExtensionHaar
  exact Metric.measure_closedBall_pos (Measure.addHaar) 0 (rootImageRadius_pos T b)

theorem rootExtensionHaar_closedBall_zero_lt_top (b : Bad (nativePlaceSelection T)) :
    rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
      (rootImageRadius T b : Real)) < ⊤ := by
  unfold rootExtensionHaar
  exact (isCompact_closedBall (0 : rootNormedExtension T b)
    (rootImageRadius_pos T b).le).measure_lt_top

theorem qBallRegion_measurable : MeasurableSet (qBallRegion T) := by
  unfold qBallRegion
  exact MeasurableSet.pi Set.countable_univ (fun b _ => measurableSet_closedBall)

theorem strictCylinder_measurable (b0 : Bad (nativePlaceSelection T)) :
    MeasurableSet (strictCylinder T b0) := by
  unfold strictCylinder
  apply MeasurableSet.pi Set.countable_univ
  intro b _
  by_cases h : b = b0
  · subst h
    simp only [if_true]
    exact measurableSet_closedBall
  · simp only [if_neg h]
    exact measurableSet_closedBall

theorem qBallRegion_measure_lt_top
    (hstrict : forall b : Bad (nativePlaceSelection T),
      ‖qPilotInThetaCarrier T b‖ < (rootImageRadius T b : Real))
    (hqpos : forall b : Bad (nativePlaceSelection T),
      0 < ‖qPilotInThetaCarrier T b‖) :
    rootExtensionProductHaar T (qBallRegion T) < ⊤ := by
  unfold rootExtensionProductHaar qBallRegion
  rw [Measure.pi_pi]
  apply ENNReal.prod_lt_top
  intro b _
  unfold rootExtensionHaar
  exact (isCompact_closedBall (qPilotInThetaCarrier T b)
    (qFitRadius_pos T hstrict hqpos b).le).measure_lt_top

theorem qBallRegion_measure_pos
    (hstrict : forall b : Bad (nativePlaceSelection T),
      ‖qPilotInThetaCarrier T b‖ < (rootImageRadius T b : Real))
    (hqpos : forall b : Bad (nativePlaceSelection T),
      0 < ‖qPilotInThetaCarrier T b‖) :
    0 < rootExtensionProductHaar T (qBallRegion T) := by
  unfold rootExtensionProductHaar qBallRegion
  rw [Measure.pi_pi]
  rw [pos_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr (fun b _ => by
    unfold rootExtensionHaar
    exact ne_of_gt (Metric.measure_closedBall_pos (Measure.addHaar) _
      (qFitRadius_pos T hstrict hqpos b)))

theorem strictCylinder_measure_pos
    (hstrict : forall b : Bad (nativePlaceSelection T),
      ‖qPilotInThetaCarrier T b‖ < (rootImageRadius T b : Real))
    (hqpos : forall b : Bad (nativePlaceSelection T),
      0 < ‖qPilotInThetaCarrier T b‖)
    (b0 : Bad (nativePlaceSelection T)) :
    0 < rootExtensionProductHaar T (strictCylinder T b0) := by
  unfold rootExtensionProductHaar strictCylinder
  rw [Measure.pi_pi]
  rw [pos_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr (fun b _ => by
    by_cases h : b = b0
    · subst h
      simp only [if_true]
      unfold rootExtensionHaar
      exact ne_of_gt (Metric.measure_closedBall_pos (Measure.addHaar) 0
        (qFitRadius_pos T hstrict hqpos b))
    · simp only [if_neg h]
      unfold rootExtensionHaar
      exact ne_of_gt (Metric.measure_closedBall_pos (Measure.addHaar) 0
        (rootImageRadius_pos T b)))

/-- **haarStrict (product Haar form)**: the q-ball has strictly smaller product
Haar measure than the actual hull.  Proof: hull contains the disjoint union of the
q ball and the strict cylinder, and the cylinder has positive measure. -/
theorem rootExtensionProductHaar_haarStrict
    (hstrict : forall b : Bad (nativePlaceSelection T),
      ‖qPilotInThetaCarrier T b‖ < (rootImageRadius T b : Real))
    (hqpos : forall b : Bad (nativePlaceSelection T),
      0 < ‖qPilotInThetaCarrier T b‖)
    (hultra : forall b, IsUltrametricDist (rootNormedExtension T b))
    (b0 : Bad (nativePlaceSelection T)) :
    rootExtensionProductHaar T (qBallRegion T) <
      rootExtensionProductHaar T (s1902Hull T) := by
  have hcylpos := strictCylinder_measure_pos T hstrict hqpos b0
  have hqfin := qBallRegion_measure_lt_top T hstrict hqpos
  have hdisj := strictCylinder_disjoint_qBall T hqpos hultra b0
  have hmeasq := qBallRegion_measurable T
  have hmeasC := strictCylinder_measurable T b0
  have hsubset : qBallRegion T ∪ strictCylinder T b0 <= s1902Hull T :=
    Set.union_subset (qBallRegion_subset_hull T hstrict hqpos)
      (strictCylinder_subset_hull T hstrict hqpos hultra b0)
  have hadd : rootExtensionProductHaar T (qBallRegion T ∪ strictCylinder T b0) =
      rootExtensionProductHaar T (qBallRegion T) +
        rootExtensionProductHaar T (strictCylinder T b0) :=
    measure_union hdisj.symm hmeasC
  have hlt : rootExtensionProductHaar T (qBallRegion T) <
      rootExtensionProductHaar T (qBallRegion T) +
        rootExtensionProductHaar T (strictCylinder T b0) :=
    ENNReal.lt_add_right (ne_of_lt hqfin) (ne_of_gt hcylpos)
  calc rootExtensionProductHaar T (qBallRegion T)
      < rootExtensionProductHaar T (qBallRegion T) +
          rootExtensionProductHaar T (strictCylinder T b0) := hlt
    _ = rootExtensionProductHaar T (qBallRegion T ∪ strictCylinder T b0) := hadd.symm
    _ <= rootExtensionProductHaar T (s1902Hull T) := measure_mono hsubset

/-- Positivity of the S1902 normalization scale (local copy; the global version
lives in Mzk1PositiveMeasureQRegionActual). -/
theorem s1902HaarScale_pos_haarStrict : 0 < s1902HaarScale T := by
  unfold s1902HaarScale
  apply ENNReal.ofReal_pos.mpr
  have hpos := (rootExtensionProductHaar_unitBall_pos_lt_top T).1
  have hlt := (rootExtensionProductHaar_unitBall_pos_lt_top T).2
  have hreal : 0 < (rootExtensionProductHaar T (rootExtensionProductUnitBall T)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hpos) (ne_of_lt hlt)
  positivity

/-- **haarStrict (normalized S1902 form)**: the normalized Haar measure of the
positive-measure q region is strictly smaller than that of the hull. -/
theorem s1902NormalizedHaar_haarStrict
    (hstrict : forall b : Bad (nativePlaceSelection T),
      ‖qPilotInThetaCarrier T b‖ < (rootImageRadius T b : Real))
    (hqpos : forall b : Bad (nativePlaceSelection T),
      0 < ‖qPilotInThetaCarrier T b‖)
    (hultra : forall b, IsUltrametricDist (rootNormedExtension T b))
    (b0 : Bad (nativePlaceSelection T)) :
    s1902NormalizedHaar T (qBallRegion T) < s1902NormalizedHaar T (s1902Hull T) := by
  have hprod := rootExtensionProductHaar_haarStrict T hstrict hqpos hultra b0
  unfold s1902NormalizedHaar
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  have h := ENNReal.mul_lt_mul_left
    (ne_of_gt (s1902HaarScale_pos_haarStrict T))
    (by simp [s1902HaarScale]) hprod
  simpa [mul_comm] using h

end LeanFormal.IUT.XiFPaper.Mzk1HaarStrictActual

end
