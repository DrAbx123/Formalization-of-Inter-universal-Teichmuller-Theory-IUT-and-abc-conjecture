/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarStrictScalingActual

/-!
# A559 annulus positivity and strict_measure from p-scaling (consumer)

Consumes the p-scaling strict ball theorem:
* the ANNULUS `s1902Hull \ rpRegion` has POSITIVE measure (additivity of product
  Haar + strict measure of the `R/p` region);
* `strict_measure` of `rpRequirement` is a theorem (no named field);
* the Cor 3.12 conclusion follows from the green `requirement_cor312`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HaarStrictRPConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

theorem rpRegion_measurable : MeasurableSet (rpRegion T) := by
  unfold rpRegion
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => Metric.isClosed_closedBall.measurableSet)

theorem hull_measurable : MeasurableSet (s1902Hull T) :=
  (s1902Hull_compact T).measurableSet

/-- **Annulus positivity** (the last geometric input): `s1902Hull \ rpRegion` has
  positive product Haar measure. -/
theorem annulus_positive :
    0 < rootExtensionProductHaar T (s1902Hull T \ rpRegion T) := by
  have hsub := rpRegion_subset_hull T
  have hmeas : MeasurableSet (s1902Hull T \ rpRegion T) :=
    (hull_measurable T).diff (rpRegion_measurable T)
  have hdisj : Disjoint (rpRegion T) (s1902Hull T \ rpRegion T) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx'.2 hx
  have hpart : rpRegion T ∪ (s1902Hull T \ rpRegion T) = s1902Hull T := by
    ext x
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact hsub h
      · exact h
    · intro hx
      by_cases hq : x ∈ rpRegion T
      · exact Or.inl hq
      · exact Or.inr ⟨hx, hq⟩
  have hadd : rootExtensionProductHaar T (rpRegion T) +
      rootExtensionProductHaar T (s1902Hull T \ rpRegion T) =
      rootExtensionProductHaar T (s1902Hull T) := by
    rw [← hpart, measure_union hdisj hmeas]
  have hlt := rpRegion_measure_lt_hull T
  have hne : rootExtensionProductHaar T (s1902Hull T \ rpRegion T) ≠ 0 := by
    intro hzero
    rw [hzero, add_zero] at hadd
    rw [hadd] at hlt
    exact lt_irrefl _ hlt
  exact pos_iff_ne_zero.mpr hne
/-- The strict measure of the resolved requirement, as a theorem. -/
theorem strict_measure_theorem :
    rpVolume T (rpRegion T) < rpVolume T (s1902Hull T) := rp_strict_measure_resolved T

/-- Cor 3.12 from the p-scaling resolved requirement. -/
theorem cor312_from_scaling (hqneg : requirementSignedQ (rpRequirement T) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (rpRequirement T) hqneg ipl hipl she hshe apt hapt) :=
  rp_cor312 T hqneg ipl hipl she hshe apt hapt

end

end LeanFormal.IUT.XiFPaper.Mzk1HaarStrictRPConsumerActual