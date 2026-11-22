import tmp.sheaf.n8.closure.EtaQRegionRepresentation
import tmp.sheaf.n8.closure.EtaRssNontrivialActual

/-!
# Eta global region at F (actual F-completion carrier)

Correct target: define the region family at the actual F place
nativeFPlaceOverBad, with local field the F-completion QCompletion.  This is
the same carrier as qORegion, so no base Fmod carrier and no push-up is used.

Actual results:
- qORegion = closed ball of radius ||q|| (nonarch multiplication of the
  integral unit ball);
- qORegion is a positive finite region;
- qO class in the actual F-level equal-volume Rss;
- actual F-level open/closed classes and their readouts.

No fabricated mass equality.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaGlobalRegionAtFActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaRssNontrivialActual
open LeanFormal.IUT.LocalFieldIntegralUnits

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [MeasurableSpace (QCompletion X)]
variable [BorelSpace (QCompletion X)]
variable [ProperSpace (QCompletion X)]
variable [IsUltrametricDist (QCompletion X)]

/-- F-level positive finite region. -/
abbrev FRegion := PositiveFiniteRegion (QCompletion X)

/-- F-level equal-volume Rss. -/
abbrev FLevelRss (μ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μ] : Type _ :=
  Quotient (SameVolume (K := QCompletion X) μ)

/-- F-level Adm predicate. -/
def FLevelAdm (μ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μ]
    (A : Set (QCompletion X)) : Prop :=
  MeasurableSet A ∧ 0 < μ A ∧ μ A < ⊤

/-- The native q is nonzero and its norm is positive. -/
theorem nativeQ_norm_pos : 0 < ‖(C9QPilotRegion.nativeQ X).q‖ :=
  norm_pos_iff.mpr (C9QPilotRegion.nativeQ X).q_ne_zero

/-- Actual qO region equals the closed ball of radius ||q||. -/
theorem qORegion_eq_closedBall :
    qORegion X =
      Metric.closedBall (0 : QCompletion X) ‖(C9QPilotRegion.nativeQ X).q‖ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_mul]
    have hy : ‖(y : QCompletion X)‖ ≤ 1 :=
      (mem_integers_iff (K := QCompletion X) _).mp y.2
    calc
      ‖(C9QPilotRegion.nativeQ X).q‖ * ‖(y : QCompletion X)‖
          ≤ ‖(C9QPilotRegion.nativeQ X).q‖ * 1 :=
        mul_le_mul_of_nonneg_left hy (norm_nonneg _)
      _ = ‖(C9QPilotRegion.nativeQ X).q‖ := mul_one _
  · intro hx
    have hq : (C9QPilotRegion.nativeQ X).q ≠ 0 :=
      (C9QPilotRegion.nativeQ X).q_ne_zero
    refine ⟨⟨x / (C9QPilotRegion.nativeQ X).q, ?_⟩, ?_⟩
    · rw [mem_integers_iff (K := QCompletion X)]
      have hxle : ‖x‖ ≤ ‖(C9QPilotRegion.nativeQ X).q‖ := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      rw [norm_div, div_le_one (nativeQ_norm_pos X)]
      exact hxle
    · field_simp [hq]

/-- Actual qO positive finite region at the F place. -/
noncomputable def qORegionPF
    (μ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μ] : FRegion X μ where
  carrier := qORegion X
  measurable := by
    rw [qORegion_eq_closedBall X]
    exact Metric.isClosed_closedBall.measurableSet
  pos := by
    rw [qORegion_eq_closedBall X]
    apply Measure.measure_pos_of_nonempty_interior
    refine ⟨(0 : QCompletion X), ?_⟩
    exact Metric.ball_subset_interior_closedBall
      (Metric.mem_ball_self (nativeQ_norm_pos X))
  finite := by
    rw [qORegion_eq_closedBall X]
    exact (isCompact_closedBall (0 : QCompletion X)
      ‖(C9QPilotRegion.nativeQ X).q‖).measure_lt_top

/-- Actual qO class in F-level Rss. -/
noncomputable def qOClass
    (μ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μ] :
    FLevelRss X μ :=
  Quotient.mk (SameVolume (K := QCompletion X) μ) (qORegionPF X μ)

/-- Actual qO readout: the F-level log-volume readout of the qO class. -/
noncomputable def qOClassReadout
    (μ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μ] : ℝ :=
  logVolumeReadout (K := QCompletion X) (mu := μ) (qOClass X μ)

theorem qOClassReadout_eq
    (μ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μ] :
    qOClassReadout X μ =
      Real.log (μ (qORegion X)).toReal :=
  logVolumeReadout_mk (K := QCompletion X) (mu := μ) (qORegionPF X μ)

/-- Actual F-level open and closed ball classes. -/
noncomputable def openClassF
    (μ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μ] : FLevelRss X μ :=
  Quotient.mk (SameVolume (K := QCompletion X) μ) (openRegion (K := QCompletion X) (mu := μ))

noncomputable def closedClassF
    (μ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μ] : FLevelRss X μ :=
  Quotient.mk (SameVolume (K := QCompletion X) μ) (closedRegion (K := QCompletion X) (mu := μ))

theorem openClassF_ne_closedClassF
    (μ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μ] :
    openClassF X μ ≠ closedClassF X μ :=
  etaRss_quotient_classes_ne (K := QCompletion X) (mu := μ)

end LeanFormal.IUT.N8Closure.EtaGlobalRegionAtFActual
