/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullLogVolumeFormulaActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import Mathlib.Tactic
/-! # #7 actual normalized-log nonpositivity and main-term bound -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ExactHullVMainTermActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeFormulaActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem normalizedLog_hull_nonpos :
    rootExtensionProductNormalizedLog T (s1902Hull T) ≤ 0 := by
  unfold rootExtensionProductNormalizedLog
  have hsub : s1902Hull T ⊆ s1902UnitRegion T := s1902Hull_subset_unitRegion T
  have hHpos : 0 < (rootExtensionProductHaar T (s1902Hull T)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (rootExtensionProductImageHull_measure_pos_lt_top (T := T)).1)
      (ne_of_lt (rootExtensionProductImageHull_measure_pos_lt_top (T := T)).2)
  have hUpos : 0 < (rootExtensionProductHaar T (s1902UnitRegion T)).toReal := by
    rw [s1902UnitRegion]
    exact ENNReal.toReal_pos (ne_of_gt (rootExtensionProductHaar_unitBall_pos_lt_top (T := T)).1)
      (ne_of_lt (rootExtensionProductHaar_unitBall_pos_lt_top (T := T)).2)
  have hle : rootExtensionProductHaar T (s1902Hull T) ≤
      rootExtensionProductHaar T (s1902UnitRegion T) := measure_mono hsub
  have hleR : (rootExtensionProductHaar T (s1902Hull T)).toReal ≤
      (rootExtensionProductHaar T (s1902UnitRegion T)).toReal :=
    ENNReal.toReal_mono (ne_of_lt (rootExtensionProductHaar_unitBall_pos_lt_top (T := T)).2) hle
  have hlog := Real.log_le_log hHpos hleR
  simp only [s1902UnitRegion] at hlog
  linarith
theorem normalizedLog_hull_le_mainTerm (logd logf : Real)
    (hmain : 0 ≤ (1 / 4 : Real) * (l.value : Real) * (logd + logf)) :
    rootExtensionProductNormalizedLog T (s1902Hull T) ≤
      (1 / 4 : Real) * (l.value : Real) * (logd + logf) :=
  (normalizedLog_hull_nonpos T).trans hmain
def rows : List String := ["normalizedLog_hull_nonpos", "normalizedLog_hull_le_mainTerm (hmain)"]
theorem rows_length : rows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1ExactHullVMainTermActual
end