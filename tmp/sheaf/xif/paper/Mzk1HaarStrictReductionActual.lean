import tmp.sheaf.xif.paper.Mzk1PositiveMeasureQRegionProofActual

/-!
# A552 reduction: annulus positivity -> strict Haar increase

The sharp half-ball issue: in a nonarchimedean field `ball(0,R/2)` can coincide
with `ball(0,R)` (same valuation class), so a strict Haar increase needs a
genuinely smaller positive-measure piece.  The proof file
`Mzk1PositiveMeasureQRegionProofActual` uses radius `R/8` (in particular it is
strictly inside the hull for every place with positive radius), and this file
proves that the **positive measure of the annulus** `hull \ qRegion` implies
the strict real Haar increase used by `strict_measure`.

The annulus positivity is the single residual geometric input (cylinder
construction with a radius-attaining theta value); all measure algebra below is
proved.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1HaarStrictReductionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem qRegion_measurable : MeasurableSet (qRegion T) := by
  unfold qRegion
  exact MeasurableSet.univ_pi (fun b => Metric.isClosed_closedBall.measurableSet)

theorem s1902Hull_measurable : MeasurableSet (s1902Hull T) :=
  (s1902Hull_compact T).measurableSet

/-- **Strict Haar increase from annulus positivity**:
`mu qRegion < mu hull` (ENNReal). -/
theorem haarStrict_of_annulus_positive
    (hann : 0 < rootExtensionProductHaar T (s1902Hull T \ qRegion T)) :
    rootExtensionProductHaar T (qRegion T) <
      rootExtensionProductHaar T (s1902Hull T) := by
  have hsub := qRegion_subset_hull T
  have hmeasC : MeasurableSet (s1902Hull T \ qRegion T) :=
    (s1902Hull_measurable T).diff (qRegion_measurable T)
  have hdisj : Disjoint (qRegion T) (s1902Hull T \ qRegion T) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx'.2 hx
  have hpart : qRegion T ∪ (s1902Hull T \ qRegion T) = s1902Hull T := by
    ext x; constructor
    · rintro (hx | ⟨hx, _⟩); exact hsub hx; exact hx
    · intro hx; by_cases hq : x ∈ qRegion T; exact Or.inl hq; exact Or.inr ⟨hx, hq⟩
  have hCeq : (qRegion T ∪ (s1902Hull T \ qRegion T)) \ qRegion T =
      s1902Hull T \ qRegion T := by
    ext x
    simp only [Set.mem_diff, Set.mem_union]
    constructor
    · intro hx
      rcases hx with ⟨hx | hx, hxq⟩
      · exact absurd hx hxq
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, hx.2⟩
  have hadd : rootExtensionProductHaar T (qRegion T) +
      rootExtensionProductHaar T (s1902Hull T \ qRegion T) =
      rootExtensionProductHaar T (s1902Hull T) := by
    rw [← hpart, measure_union hdisj hmeasC]
    rw [hCeq]
  have hqfin : rootExtensionProductHaar T (qRegion T) ≠ ⊤ := ne_of_lt (qRegion_measure_lt_top T)
  rw [← hadd]
  exact ENNReal.lt_add_right hqfin (ne_of_gt hann)

/-- Real form of the strict Haar increase. -/
theorem haarStrict_toReal_of_annulus_positive
    (hann : 0 < rootExtensionProductHaar T (s1902Hull T \ qRegion T)) :
    (rootExtensionProductHaar T (qRegion T)).toReal <
      (rootExtensionProductHaar T (s1902Hull T)).toReal := by
  have hqfin : rootExtensionProductHaar T (qRegion T) ≠ ⊤ := ne_of_lt (qRegion_measure_lt_top T)
  have hhfin : rootExtensionProductHaar T (s1902Hull T) ≠ ⊤ := by
    rw [s1902Hull]
    exact ne_of_lt (rootExtensionProductImageHull_measure_pos_lt_top (T := T)).2
  exact (ENNReal.toReal_lt_toReal hqfin hhfin).mpr (haarStrict_of_annulus_positive T hann)

/-- Resolved normalized volume: from annulus positivity both `q_pos` and
`strict_measure` are theorems. -/
theorem resolved_strict_measure_of_annulus_positive
    (hann : 0 < rootExtensionProductHaar T (s1902Hull T \ qRegion T)) :
    qNormalizedVolume T (qRegion T) < qNormalizedVolume T (s1902Hull T) := by
  have hlt := haarStrict_toReal_of_annulus_positive T hann
  have hpos : 0 < (rootExtensionProductHaar T (qRegion T)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (qRegion_measure_pos T)) (ne_of_lt (qRegion_measure_lt_top T))
  exact qNormalizedVolume_strict_of_haarStrict T hpos hlt

end LeanFormal.IUT.XiFPaper.Mzk1HaarStrictReductionActual
