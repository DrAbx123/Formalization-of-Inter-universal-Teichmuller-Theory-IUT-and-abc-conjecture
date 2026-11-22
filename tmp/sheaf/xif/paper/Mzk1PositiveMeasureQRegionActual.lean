/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import Mathlib.Tactic

/-! # A551: positive-measure q-pilot region (eliminating `q_pos`)

The old `KummerXiERealization` used the singleton `{qPilotInThetaCarrier}`, whose
Haar measure is zero; hence `q_pos`/`strict_measure` could not be derived from the
real Haar log-volume (shehdd's singleton-null computation).  This file replaces the
singleton by a positive-measure PRODUCT BALL around the transported q-pilot image:

  qRegion = Set.pi univ (fun b => closedBall (qPilotInThetaCarrier b) (qMargin b)),

with `qMargin b = (rootImageRadius b - ||q b||) / 2`.

PROVED here (under the paper-geometric strict-inside hypothesis
`hstrict : forall b, ||q b|| < rootImageRadius b`):

* `qMargin_pos`: the margin is positive;
* `qRegion_subset_hull`: qRegion lies in the actual Theta hull s1902Hull (using the
  distance triangle inequality and the hull radius);
* `qRegion_measurable`: it is Borel;
* `rootExtensionProductHaar_qRegion_pos_lt_top`: its actual product Haar measure is
  positive and finite (product of local closed-ball masses, using
  `Metric.measure_closedBall_pos`);
* `s1902NormalizedHaar_qRegion_pos_lt_top`: hence positive and finite for the
  normalized S1902 Haar (positive rescaling);
* `qRegionVolume_pos`: `0 < (s1902NormalizedHaar qRegion).toReal` — the former
  named `q_pos` is now a THEOREM for the positive-measure region.

Remaining named (minimal) input: `annulus_positive`, i.e.
`mu qRegion < mu s1902Hull` strictly.  This is a pure measure-theoretic fact
`hull is strictly larger than the q ball, so the annulus has positive Haar mass`.
It replaces `strict_measure` by a concrete measurable-set statement; proving it
needs the nonarchimedean ball-measure formula (measure of a ball of radius r is
proportional to r), which is not currently available in the repository API.
The containment qRegion <= hull together with monotonicity gives the non-strict
inequality as a theorem here. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open MeasureTheory
open scoped ENNReal BigOperators Pointwise

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The radial margin of the q-pilot image inside the hull. -/
noncomputable def qMargin (b : Bad (nativePlaceSelection T)) : Real :=
  (LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual.LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual.rootImageRadius T b - ‖qPilotInThetaCarrier T b‖) / 2

theorem qMargin_pos (hstrict : forall b : Bad (nativePlaceSelection T),
    ‖qPilotInThetaCarrier T b‖ < (LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual.rootImageRadius T b : Real))
    (b : Bad (nativePlaceSelection T)) : 0 < qMargin T b := by
  unfold qMargin
  have h := hstrict b
  nlinarith

/-- The positive-measure q-pilot region: a product of closed balls around the
transported q-pilot image, with radial margin strictly inside the hull. -/
noncomputable def qRegion : Set (S1902Carrier T) :=
  Set.pi Set.univ (fun b => Metric.closedBall (qPilotInThetaCarrier T b) (qMargin T b))

/-- qRegion lies in the actual Theta hull. -/
theorem qRegion_subset_hull (hstrict : forall b : Bad (nativePlaceSelection T),
    ‖qPilotInThetaCarrier T b‖ < (LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual.rootImageRadius T b : Real)) :
    qRegion T <= s1902Hull T := by
  intro x hx
  unfold s1902Hull rootExtensionProductImageHull
  rw [Set.mem_pi]
  intro b _
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hxb : x b ∈ Metric.closedBall (qPilotInThetaCarrier T b) (qMargin T b) :=
    hx b (Set.mem_univ b)
  rw [Metric.mem_closedBall] at hxb
  have hxb_norm : ‖x b - qPilotInThetaCarrier T b‖ <= qMargin T b := by
    rw [← dist_eq_norm]
    exact hxb
  calc ‖x b - 0‖ = ‖(x b - qPilotInThetaCarrier T b) +
        qPilotInThetaCarrier T b‖ := by rw [sub_add_cancel]
    _ <= ‖x b - qPilotInThetaCarrier T b‖ + ‖qPilotInThetaCarrier T b‖ :=
        norm_add_le _ _
    _ <= qMargin T b + ‖qPilotInThetaCarrier T b‖ :=
        add_le_add_right hxb_norm _
    _ = (LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual.rootImageRadius T b + ‖qPilotInThetaCarrier T b‖) / 2 := by
        unfold qMargin; ring
    _ < (LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual.rootImageRadius T b : Real) := by
        have := hstrict b; nlinarith

/-- qRegion is Borel measurable. -/
theorem qRegion_measurable : MeasurableSet (qRegion T) := by
  unfold qRegion
  exact MeasurableSet.pi Set.countable_univ (fun b _ => measurableSet_closedBall)

/-- Local closed-ball Haar mass is positive and finite. -/
theorem rootExtensionHaar_closedBall_pos_lt_top
    (hstrict : forall b : Bad (nativePlaceSelection T),
      ‖qPilotInThetaCarrier T b‖ < (LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual.rootImageRadius T b : Real))
    (b : Bad (nativePlaceSelection T)) :
    0 < rootExtensionHaar T b (Metric.closedBall (qPilotInThetaCarrier T b) (qMargin T b)) ∧
      rootExtensionHaar T b (Metric.closedBall (qPilotInThetaCarrier T b) (qMargin T b)) < ⊤ := by
  constructor
  · unfold rootExtensionHaar
    exact Metric.measure_closedBall_pos (Measure.addHaar) _ (qMargin_pos T hstrict b)
  · unfold rootExtensionHaar
    exact (isCompact_closedBall (qPilotInThetaCarrier T b)
      (qMargin_pos T hstrict b).le).measure_lt_top

/-- Actual product Haar measure of qRegion: positive and finite. -/
theorem rootExtensionProductHaar_qRegion_pos_lt_top
    (hstrict : forall b : Bad (nativePlaceSelection T),
      ‖qPilotInThetaCarrier T b‖ < (LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual.rootImageRadius T b : Real)) :
    0 < rootExtensionProductHaar T (qRegion T) ∧
      rootExtensionProductHaar T (qRegion T) < ⊤ := by
  unfold rootExtensionProductHaar qRegion
  rw [Measure.pi_pi]
  · constructor
    · rw [pos_iff_ne_zero]
      exact Finset.prod_ne_zero_iff.mpr (fun b _ =>
        ne_of_gt (rootExtensionHaar_closedBall_pos_lt_top T hstrict b).1)
    · apply ENNReal.prod_lt_top
      intro b _
      exact (rootExtensionHaar_closedBall_pos_lt_top T hstrict b).2

/-- The positive rescaling factor of the normalized S1902 Haar is positive. -/
theorem s1902HaarScale_pos : 0 < s1902HaarScale T := by
  unfold s1902HaarScale
  apply ENNReal.ofReal_pos.mpr
  have hpos := (rootExtensionProductHaar_unitBall_pos_lt_top T).1
  have hlt := (rootExtensionProductHaar_unitBall_pos_lt_top T).2
  have hreal : 0 < (rootExtensionProductHaar T (rootExtensionProductUnitBall T)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hpos) (ne_of_lt hlt)
  positivity

/-- Normalized S1902 Haar measure of qRegion: positive and finite. -/
theorem s1902NormalizedHaar_qRegion_pos_lt_top
    (hstrict : forall b : Bad (nativePlaceSelection T),
      ‖qPilotInThetaCarrier T b‖ < (LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual.rootImageRadius T b : Real)) :
    0 < s1902NormalizedHaar T (qRegion T) ∧ s1902NormalizedHaar T (qRegion T) < ⊤ := by
  have hprod := rootExtensionProductHaar_qRegion_pos_lt_top T hstrict
  unfold s1902NormalizedHaar
  rw [Measure.smul_apply, smul_eq_mul]
  constructor
  · exact ENNReal.mul_pos (ne_of_gt (s1902HaarScale_pos T)) (ne_of_gt hprod.1)
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hprod.2

/-- The former named `q_pos`: the real normalized measure of the positive-measure
q-pilot region is strictly positive. -/
theorem qRegionVolume_pos
    (hstrict : forall b : Bad (nativePlaceSelection T),
      ‖qPilotInThetaCarrier T b‖ < (LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual.rootImageRadius T b : Real)) :
    0 < (s1902NormalizedHaar T (qRegion T)).toReal := by
  have h := s1902NormalizedHaar_qRegion_pos_lt_top T hstrict
  exact ENNReal.toReal_pos (ne_of_gt h.1) (ne_of_lt h.2)

/-- Non-strict measure comparison qRegion <= hull (from containment + monotonicity). -/
theorem s1902NormalizedHaar_qRegion_le_hull
    (hstrict : forall b : Bad (nativePlaceSelection T),
      ‖qPilotInThetaCarrier T b‖ < (LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual.rootImageRadius T b : Real)) :
    s1902NormalizedHaar T (qRegion T) <= s1902NormalizedHaar T (s1902Hull T) :=
  measure_mono (qRegion_subset_hull T hstrict)

/-- The remaining minimal named input: strict increase of the normalized Haar mass
of the hull over the positive-measure q ball (the ball-annulus has positive mass). -/
def AnnulusPositive (hstrict : forall b : Bad (nativePlaceSelection T),
    ‖qPilotInThetaCarrier T b‖ < (LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual.rootImageRadius T b : Real)) : Prop :=
  s1902NormalizedHaar T (qRegion T) < s1902NormalizedHaar T (s1902Hull T)

/-- Data package: positive-measure q region with PROVED positivity/containment and
the single remaining named annulus condition (replacement of `strict_measure`). -/
structure PositiveMeasureQRegionData
    (hstrict : forall b : Bad (nativePlaceSelection T),
      ‖qPilotInThetaCarrier T b‖ < (LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual.rootImageRadius T b : Real)) where
  region_eq : Set (S1902Carrier T) = qRegion T
  subset_hull : qRegion T <= s1902Hull T
  measurable : MeasurableSet (qRegion T)
  volume_pos : 0 < (s1902NormalizedHaar T (qRegion T)).toReal
  volume_finite : s1902NormalizedHaar T (qRegion T) < ⊤
  annulus_positive : AnnulusPositive T hstrict

noncomputable def positiveMeasureQRegionData
    (hstrict : forall b : Bad (nativePlaceSelection T),
      ‖qPilotInThetaCarrier T b‖ < (LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual.rootImageRadius T b : Real))
    (hann : AnnulusPositive T hstrict) : PositiveMeasureQRegionData T hstrict where
  region_eq := rfl
  subset_hull := qRegion_subset_hull T hstrict
  measurable := qRegion_measurable T
  volume_pos := qRegionVolume_pos T hstrict
  volume_finite := (s1902NormalizedHaar_qRegion_pos_lt_top T hstrict).2
  annulus_positive := hann

end LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionActual

end
