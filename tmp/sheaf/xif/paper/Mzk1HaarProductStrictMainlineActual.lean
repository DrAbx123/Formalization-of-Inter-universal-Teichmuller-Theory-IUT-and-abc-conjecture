/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarScalingOneDimActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-!
# A581 mainline product strictness (independent clean file)

Product strictness of the `R/p` region vs the actual hull, using the green mainline
1D strictness `Mzk1HaarScalingOneDimActual.rootExtensionHaar_ball_strict` and
`Finset.prod_lt_prod` through `Measure.pi_pi`/`ENNReal.toReal_prod`.

The result is the resolved xi-e requirement (`strict_measure` theorem) and the
green `Cor312Conclusion`; no dependency on hull-owned product/scaling files.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open MeasureTheory
open scoped Pointwise ENNReal BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

noncomputable def rpRadius (b : Bad (nativePlaceSelection T)) : ℝ :=
  (rootImageRadius T b : ℝ) / (qVFamTensorP T b : ℝ)

theorem rpRadius_pos (b : Bad (nativePlaceSelection T)) : 0 < rpRadius T b :=
  div_pos (NNReal.coe_pos.mpr (rootImageRadius_pos (T := T) (b := b)))
    (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos)

noncomputable def rpRegion : Set (S1902Carrier T) :=
  Set.pi Set.univ (fun b => Metric.closedBall (0 : rootNormedExtension T b) (rpRadius T b))

noncomputable def fullRegion : Set (S1902Carrier T) :=
  Set.pi Set.univ (fun b => Metric.closedBall (0 : rootNormedExtension T b)
    (rootImageRadius T b : ℝ))

theorem fullRegion_eq_hull : fullRegion T = s1902Hull T := rfl

theorem rpRegion_subset_full : rpRegion T ⊆ fullRegion T := by
  intro x hx b _
  have hxb := hx b (Set.mem_univ b)
  rw [Metric.mem_closedBall] at hxb ⊢
  rw [dist_zero_right] at hxb ⊢
  have hp : (1 : ℝ) ≤ (qVFamTensorP T b : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt.le
  calc ‖x b‖ ≤ rpRadius T b := hxb
    _ = (rootImageRadius T b : ℝ) / (qVFamTensorP T b : ℝ) := rfl
    _ ≤ (rootImageRadius T b : ℝ) / 1 := by gcongr
    _ = (rootImageRadius T b : ℝ) := div_one _

theorem rpRegion_subset_hull : rpRegion T ⊆ s1902Hull T := by
  rw [← fullRegion_eq_hull T]
  exact rpRegion_subset_full T

theorem rpRegion_measure_pos : 0 < rootExtensionProductHaar T (rpRegion T) := by
  unfold rpRegion rootExtensionProductHaar
  rw [Measure.pi_pi, pos_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr (fun b _ =>
    ne_of_gt (rootExtensionClosedBall_measure_pos (T := T) (b := b) _ (rpRadius_pos T b)))

theorem rpRegion_measure_lt_top : rootExtensionProductHaar T (rpRegion T) < ⊤ := by
  unfold rpRegion rootExtensionProductHaar
  rw [Measure.pi_pi]
  apply ENNReal.prod_lt_top
  intro b _
  exact rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _

theorem fullRegion_measure_lt_top : rootExtensionProductHaar T (fullRegion T) < ⊤ := by
  rw [fullRegion_eq_hull T]
  exact (rootExtensionProductImageHull_measure_pos_lt_top (T := T)).2

theorem rpRegion_toReal :
    (rootExtensionProductHaar T (rpRegion T)).toReal =
      ∏ b : Bad (nativePlaceSelection T),
        (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
          (rpRadius T b))).toReal := by
  unfold rpRegion rootExtensionProductHaar
  rw [Measure.pi_pi, ENNReal.toReal_prod]

theorem fullRegion_toReal :
    (rootExtensionProductHaar T (fullRegion T)).toReal =
      ∏ b : Bad (nativePlaceSelection T),
        (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
          (rootImageRadius T b : ℝ))).toReal := by
  unfold fullRegion rootExtensionProductHaar
  rw [Measure.pi_pi, ENNReal.toReal_prod]

theorem rpRegion_measure_lt_hull :
    rootExtensionProductHaar T (rpRegion T) < rootExtensionProductHaar T (s1902Hull T) := by
  rw [← fullRegion_eq_hull T]
  refine (ENNReal.toReal_lt_toReal (ne_of_lt (rpRegion_measure_lt_top T))
    (ne_of_lt (fullRegion_measure_lt_top T))).mp ?_
  rw [rpRegion_toReal, fullRegion_toReal]
  apply Finset.prod_lt_prod
  · intro b _
    exact ENNReal.toReal_pos
      (ne_of_gt (rootExtensionClosedBall_measure_pos (T := T) (b := b) _
        (rpRadius_pos T b)))
      (ne_of_lt (rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _))
  · intro b _
    exact ENNReal.toReal_mono
      (ne_of_lt (rootExtensionClosedBall_measure_lt_top (T := T) (b := b)
        (rootImageRadius T b : ℝ)))
      (le_of_lt (by
        simpa [rpRadius] using rootExtensionHaar_ball_strict T b
          (rootImageRadius T b)
          (NNReal.coe_pos.mpr (rootImageRadius_pos (T := T) (b := b)))))
  · let b0 := Classical.choice (inferInstance : Nonempty (Bad (nativePlaceSelection T)))
    have hb0 : ((rootExtensionHaar T b0) (Metric.closedBall
          (0 : rootNormedExtension T b0) (rpRadius T b0))).toReal <
        ((rootExtensionHaar T b0) (Metric.closedBall
          (0 : rootNormedExtension T b0) (rootImageRadius T b0 : ℝ))).toReal := by
      refine (ENNReal.toReal_lt_toReal
        (ne_of_lt (rootExtensionClosedBall_measure_lt_top (T := T) (b := b0)
          (rpRadius T b0)))
        (ne_of_lt (rootExtensionClosedBall_measure_lt_top (T := T) (b := b0)
          (rootImageRadius T b0 : ℝ)))).mpr ?_
      simpa [rpRadius] using rootExtensionHaar_ball_strict T b0
        (rootImageRadius T b0)
        (NNReal.coe_pos.mpr (rootImageRadius_pos (T := T) (b := b0)))
    exact ⟨b0, Finset.mem_univ b0, hb0⟩

theorem rpRegion_measure_lt_full :
    rootExtensionProductHaar T (rpRegion T) < rootExtensionProductHaar T (fullRegion T) := by
  simpa [fullRegion_eq_hull T] using rpRegion_measure_lt_hull T
noncomputable def rpVolume (S : Set (S1902Carrier T)) : ℝ :=
  (rootExtensionProductHaar T S).toReal

def rpRequirement : XiEContainmentRequirement (S1902Carrier T) (rpVolume T) where
  qRegion := rpRegion T
  thetaPossibleImages := rpRegion T
  hullRegion := s1902Hull T
  q_in_possible := fun _ hx => hx
  possible_in_hull := rpRegion_subset_hull T
  q_pos := ENNReal.toReal_pos (ne_of_gt (rpRegion_measure_pos T))
    (ne_of_lt (rpRegion_measure_lt_top T))
  strict_measure := by
    change (rootExtensionProductHaar T (rpRegion T)).toReal <
      (rootExtensionProductHaar T (s1902Hull T)).toReal
    rw [← fullRegion_eq_hull T]
    exact (ENNReal.toReal_lt_toReal (ne_of_lt (rpRegion_measure_lt_top T))
      (ne_of_lt (fullRegion_measure_lt_top T))).mpr (rpRegion_measure_lt_full T)

theorem rp_strict_measure_resolved :
    rpVolume T (rpRegion T) < rpVolume T (s1902Hull T) :=
  (rpRequirement T).strict_measure

theorem rp_cor312 (hqneg : requirementSignedQ (rpRequirement T) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (rpRequirement T) hqneg ipl hipl she hshe apt hapt) :=
  requirement_cor312 (rpRequirement T) hqneg ipl hipl she hshe apt hapt

end LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual

end
