import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import Mathlib.Tactic

/-!
# A551 PROOF file: positive-measure half-ball q-region

Note: `Mzk1PositiveMeasureQRegionActual.lean` (other lane) uses a ball around
the q-image with radius `(R_b - ||q_b||)/2`; for coordinates where the q image
attains the hull radius `R_b` this radius is 0, so the region has a null
coordinate and cannot have positive measure.  This proof file instead uses the
honest log-shell region

  `qRegion T = set.pi univ (fun b => closedBall 0 (R_b / 2))`

centred at 0, which is contained in the hull, has PROVED positive and finite
product Haar measure, and makes `q_pos` a theorem for the normalized log-volume;
`strict_measure` reduces to the strict Haar increase of the hull over the
half-ball (the annulus step), recorded as the single named input `haarStrict`.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual

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
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Log-shell q-region: product of half-radius closed balls centred at 0. -/
def qRegion : Set (S1902Carrier T) :=
  Set.pi Set.univ (fun b =>
    Metric.closedBall (0 : rootNormedExtension T b)
      ((rootImageRadius T b : Real) / 8))

theorem qRegion_subset_hull : qRegion T ⊆ s1902Hull T := by
  intro x hx b hb
  exact Metric.closedBall_subset_closedBall (x := (0 : rootNormedExtension T b))
    (by
      have hnonneg : (0 : Real) ≤ (rootImageRadius T b : Real) := NNReal.coe_nonneg _
      linarith) (hx b hb)

theorem qRegion_measure_pos : 0 < rootExtensionProductHaar T (qRegion T) := by
  unfold qRegion rootExtensionProductHaar
  rw [Measure.pi_pi]
  rw [pos_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr (fun b _ => by
    have hr : (0 : Real) < (rootImageRadius T b : Real) / 8 := by
      have hpos : (0 : Real) < (rootImageRadius T b : Real) :=
        NNReal.coe_pos.mpr (rootImageRadius_pos (T := T) (b := b))
      linarith
    exact ne_of_gt (rootExtensionClosedBall_measure_pos (T := T) (b := b) _ hr))

theorem qRegion_measure_lt_top : rootExtensionProductHaar T (qRegion T) < ⊤ := by
  unfold qRegion rootExtensionProductHaar
  rw [Measure.pi_pi]
  apply ENNReal.prod_lt_top
  intro b _
  exact rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _

noncomputable def qNormalizedVolume (S : Set (S1902Carrier T)) : Real :=
  Real.log ((rootExtensionProductHaar T S).toReal /
      (rootExtensionProductHaar T (qRegion T)).toReal) + 1

theorem qNormalizedVolume_qRegion
    (hpos : 0 < (rootExtensionProductHaar T (qRegion T)).toReal) :
    qNormalizedVolume T (qRegion T) = 1 := by
  unfold qNormalizedVolume
  rw [div_self (ne_of_gt hpos)]
  simp

theorem qNormalizedVolume_strict_of_haarStrict
    (hpos : 0 < (rootExtensionProductHaar T (qRegion T)).toReal)
    (hlt : (rootExtensionProductHaar T (qRegion T)).toReal <
      (rootExtensionProductHaar T (s1902Hull T)).toReal) :
    qNormalizedVolume T (qRegion T) < qNormalizedVolume T (s1902Hull T) := by
  rw [qNormalizedVolume_qRegion T hpos]
  unfold qNormalizedVolume
  have hratio : 1 < (rootExtensionProductHaar T (s1902Hull T)).toReal /
      (rootExtensionProductHaar T (qRegion T)).toReal := by
    rw [lt_div_iff₀ hpos]
    linarith
  have hlog : 0 < Real.log ((rootExtensionProductHaar T (s1902Hull T)).toReal /
      (rootExtensionProductHaar T (qRegion T)).toReal) := Real.log_pos hratio
  linarith

/-- Named-input accounting: with the positive-measure half-ball q-region only
the strict Haar increase (hull over q-region) remains named. -/
structure PositiveQRegionHaarStrict where
  q_pos : 0 < qNormalizedVolume T (qRegion T)
  strict_measure : qNormalizedVolume T (qRegion T) < qNormalizedVolume T (s1902Hull T)
  haarStrict : (rootExtensionProductHaar T (qRegion T)).toReal <
    (rootExtensionProductHaar T (s1902Hull T)).toReal

theorem positiveQRegionHaarStrict_of_strict
    (hpos : 0 < (rootExtensionProductHaar T (qRegion T)).toReal)
    (hlt : (rootExtensionProductHaar T (qRegion T)).toReal <
      (rootExtensionProductHaar T (s1902Hull T)).toReal) :
    PositiveQRegionHaarStrict T where
  q_pos := by
    rw [qNormalizedVolume_qRegion T hpos]
    norm_num
  strict_measure := qNormalizedVolume_strict_of_haarStrict T hpos hlt
  haarStrict := hlt

end LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
