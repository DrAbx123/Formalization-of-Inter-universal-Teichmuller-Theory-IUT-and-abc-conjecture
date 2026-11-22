/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeV2Actual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.Mzk1HullLogVolumeFormulaActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import Mathlib.Tactic
/-! # Route C0 global q-lattice readout: subset and normalized-log bound -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0RouteC0GlobalReadoutActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeFormulaActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open MeasureTheory
open scoped BigOperators
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]
/-- Global q product lattice is contained in the actual theta image hull. -/
theorem c0ProductQ_subset_thetaHull :
    c0ProductQ T ⊆ rootExtensionProductImageHull T :=
  c0ProductQ_subset_imageHull T
/-- Global q product Haar is at most the hull Haar. -/
theorem c0ProductQ_haar_le_thetaHull :
    rootExtensionProductHaar T (c0ProductQ T) ≤
      rootExtensionProductHaar T (rootExtensionProductImageHull T) :=
  c0ProductHaar_le_imageHull T
/-- Normalized-log bound: the q product normalized log is at most the theta
hull normalized log, under actual positivity/finiteness of the two measures. -/
theorem c0ProductQ_normalizedLog_le_thetaHull
    (hQ0 : rootExtensionProductHaar T (c0ProductQ T) ≠ 0)
    (hQtop : rootExtensionProductHaar T (c0ProductQ T) ≠ ⊤)
    (hH0 : rootExtensionProductHaar T (rootExtensionProductImageHull T) ≠ 0)
    (hHtop : rootExtensionProductHaar T (rootExtensionProductImageHull T) ≠ ⊤) :
    rootExtensionProductNormalizedLog T (c0ProductQ T) ≤
      rootExtensionProductNormalizedLog T (rootExtensionProductImageHull T) := by
  have hm : rootExtensionProductHaar T (c0ProductQ T) ≤
      rootExtensionProductHaar T (rootExtensionProductImageHull T) :=
    c0ProductQ_haar_le_thetaHull T
  have hto : (rootExtensionProductHaar T (c0ProductQ T)).toReal ≤
      (rootExtensionProductHaar T (rootExtensionProductImageHull T)).toReal :=
    ENNReal.toReal_mono hHtop hm
  have hQpos : 0 < (rootExtensionProductHaar T (c0ProductQ T)).toReal :=
    ENNReal.toReal_pos hQ0 hQtop
  have hlog : Real.log (rootExtensionProductHaar T (c0ProductQ T)).toReal ≤
      Real.log (rootExtensionProductHaar T (rootExtensionProductImageHull T)).toReal :=
    Real.log_le_log hQpos hto
  unfold rootExtensionProductNormalizedLog
  linarith
/-- The theta hull normalized log is exactly s1915ClosedForm - 1. -/
theorem thetaHull_normalizedLog_eq_closedForm_sub_one :
    rootExtensionProductNormalizedLog T (rootExtensionProductImageHull T) =
      s1915ClosedForm T - 1 := by
  change rootExtensionProductNormalizedLog T
    (LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual.s1902Hull T) =
    s1915ClosedForm T - 1
  rw [normalizedLog_hull_eq_sum_diff T]
  unfold s1915ClosedForm
  have hterm : ∀ b : Bad (nativePlaceSelection T),
      Real.log (rootExtensionHaar T b
        (Metric.closedBall (0 : rootNormedExtension T b)
          ((rootImageRadius T b : NNReal) : Real))).toReal -
        Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal =
      (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real) := by
    intro b
    have hfac := s1915_local_measure T b
    rw [hfac]
    rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
    have hr : 0 < (rootImageRadius T b : Real) := by
      exact_mod_cast rootImageRadius_pos (T := T) (b := b)
    have hpow : 0 < (rootImageRadius T b : Real) ^ s1915LocalDegree T b :=
      pow_pos hr _
    rw [Real.log_mul hpow.ne'
      (ENNReal.toReal_pos
        (ne_of_gt (rootExtensionUnitBall_measure_pos T b))
        (ne_of_lt (rootExtensionUnitBall_measure_lt_top T b))).ne']
    rw [Real.log_pow]
    ring
  rw [Finset.sum_congr rfl (fun b _ => hterm b)]
  ring
/-- Original-target normalized form: q product normalized log <= s1915ClosedForm - 1. -/
theorem c0ProductQ_normalizedLog_le_closedForm_sub_one
    (hQ0 : rootExtensionProductHaar T (c0ProductQ T) ≠ 0)
    (hQtop : rootExtensionProductHaar T (c0ProductQ T) ≠ ⊤)
    (hH0 : rootExtensionProductHaar T (rootExtensionProductImageHull T) ≠ 0)
    (hHtop : rootExtensionProductHaar T (rootExtensionProductImageHull T) ≠ ⊤) :
    rootExtensionProductNormalizedLog T (c0ProductQ T) ≤
      s1915ClosedForm T - 1 := by
  have hq := c0ProductQ_normalizedLog_le_thetaHull T hQ0 hQtop hH0 hHtop
  have hh := thetaHull_normalizedLog_eq_closedForm_sub_one T
  linarith
end LeanFormal.IUT.XiFPaper.Mzk1P0RouteC0GlobalReadoutActual
end