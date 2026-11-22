import tmp.sheaf.xif.paper.Mzk1A1DeltaExplicitActual
import tmp.sheaf.xif.paper.Mzk1P3ProductHaarPiActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.Mzk1P0RouteC0GlobalReadoutActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
/-! #A1.6 product consumer: global q-lattice normalized log = sum local signed
terms = s1915ClosedForm - 1 - totalDelta, and hence <= s1915ClosedForm - 1.
`totalDelta = sum_b d_b*a1Delta_b >= 0` is the explicit positive correction. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1A1SignedReadoutProductActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1A1DeltaExplicitActual
open LeanFormal.IUT.XiFPaper.Mzk1P3ProductHaarPiActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1P0RouteC0GlobalReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Total explicit A1.6 delta over all bad places. -/
noncomputable def totalDelta : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    (s1915LocalDegree T b : Real) * a1Delta (T := T) (b := b)
/-- Global q-lattice normalized log is the sum of the local signed q-logs. -/
theorem productQ_normalizedLog_eq_sum_a1LocalQLog
    (hQ0 : ∀ b, rootExtensionHaar T b (c0QLattice T b) ≠ 0)
    (hQtop : ∀ b, rootExtensionHaar T b (c0QLattice T b) ≠ ⊤)
    (hO0 : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hOtop : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤) :
    rootExtensionProductNormalizedLog T (c0ProductQ T) =
      ∑ b : Bad (nativePlaceSelection T), a1LocalQLog (T := T) (b := b) := by
  simpa [c0ProductQ, a1LocalQLog] using
    productNormalizedLog_pi T (fun b => c0QLattice T b) hQ0 hQtop hO0 hOtop
/-- Local signed term equals `d*log r - d*a1Delta`. -/
theorem a1LocalQLog_eq_degree_log_radius_sub_degree_delta
    (hd : 0 < s1915LocalDegree T b) :
    a1LocalQLog (T := T) (b := b) =
      (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real) -
        (s1915LocalDegree T b : Real) * a1Delta (T := T) (b := b) := by
  have hdpos : (0 : Real) < (s1915LocalDegree T b : Real) := by exact_mod_cast hd
  have hid := a1SignedTerm_eq_log_radius_sub_delta (T := T) (b := b)
  unfold a1SignedTerm at hid
  have hmul := congrArg (fun x => (s1915LocalDegree T b : Real) * x) hid
  have hleft : (s1915LocalDegree T b : Real) *
      ((1 / (s1915LocalDegree T b : Real)) *
        (Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
          Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal)) =
      a1LocalQLog (T := T) (b := b) := by
    unfold a1LocalQLog
    field_simp [ne_of_gt hdpos]
  rw [hleft] at hmul
  rw [hmul]
  ring
/-- Sum of local signed logs equals `sum d*log r - totalDelta`. -/
theorem sum_a1LocalQLog_eq_degree_log_radius_sub_totalDelta
    (hd : ∀ b, 0 < s1915LocalDegree T b) :
    (∑ b : Bad (nativePlaceSelection T), a1LocalQLog (T := T) (b := b)) =
      (∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) * Real.log (rootImageRadius T b : Real)) -
        totalDelta T := by
  unfold totalDelta
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  exact a1LocalQLog_eq_degree_log_radius_sub_degree_delta (T := T) (b := b) (hd b)
/-- `totalDelta` is nonnegative. -/
theorem totalDelta_nonneg
    (hd : ∀ b, 0 < s1915LocalDegree T b)
    (hQ0 : ∀ b, rootExtensionHaar T b (c0QLattice T b) ≠ 0)
    (hQtop : ∀ b, rootExtensionHaar T b (c0QLattice T b) ≠ ⊤)
    (hO0 : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hOtop : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤) :
    0 ≤ totalDelta T := by
  unfold totalDelta
  apply Finset.sum_nonneg
  intro b _
  have hb := a1Delta_nonneg (T := T) (b := b) (hd b) (hQ0 b) (hQtop b) (hO0 b) (hOtop b)
  exact mul_nonneg (Nat.cast_nonneg _) hb
/-- A1.6 product form:
`globalNormalizedLog = s1915ClosedForm - 1 - totalDelta`. -/
theorem productQ_normalizedLog_eq_closedForm_sub_one_sub_totalDelta
    (hQ0 : ∀ b, rootExtensionHaar T b (c0QLattice T b) ≠ 0)
    (hQtop : ∀ b, rootExtensionHaar T b (c0QLattice T b) ≠ ⊤)
    (hO0 : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hOtop : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤)
    (hd : ∀ b, 0 < s1915LocalDegree T b) :
    rootExtensionProductNormalizedLog T (c0ProductQ T) =
      s1915ClosedForm T - 1 - totalDelta T := by
  rw [productQ_normalizedLog_eq_sum_a1LocalQLog T hQ0 hQtop hO0 hOtop]
  rw [sum_a1LocalQLog_eq_degree_log_radius_sub_totalDelta T hd]
  unfold s1915ClosedForm
  ring
/-- A1.6 consumer: global q normalized log <= s1915ClosedForm - 1. -/
theorem productQ_normalizedLog_le_closedForm_sub_one
    (hQ0 : ∀ b, rootExtensionHaar T b (c0QLattice T b) ≠ 0)
    (hQtop : ∀ b, rootExtensionHaar T b (c0QLattice T b) ≠ ⊤)
    (hO0 : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hOtop : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤)
    (hd : ∀ b, 0 < s1915LocalDegree T b) :
    rootExtensionProductNormalizedLog T (c0ProductQ T) ≤
      s1915ClosedForm T - 1 := by
  rw [productQ_normalizedLog_eq_closedForm_sub_one_sub_totalDelta T hQ0 hQtop hO0 hOtop hd]
  have hδ := totalDelta_nonneg T hd hQ0 hQtop hO0 hOtop
  linarith
end LeanFormal.IUT.XiFPaper.Mzk1A1SignedReadoutProductActual
end