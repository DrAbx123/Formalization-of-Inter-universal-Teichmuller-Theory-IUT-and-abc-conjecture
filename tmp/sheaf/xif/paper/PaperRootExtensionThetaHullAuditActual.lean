import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullActual
import tmp.sheaf.xif.paper.PaperRootExtensionNormBoundActual

/-!
# Audit: actual coordinatewise minimal image hull

The previous rootExtensionProductThetaHull was definitionally the full product
unit ball, so its relative log was definitionally zero.  Here the hull is the
smallest product of coordinatewise closed norm balls containing the actual root
Theta image: radius r b = max_j ||rootThetaValue j b||.  The image is contained
by construction; the hull may be strictly smaller than the full unit ball.  Its
Haar measure is positive finite and the normalized log is relative to the full
product unit ball, not definitionally zero.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionNormBoundActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Coordinatewise maximal root image norm (NNReal radius). -/
noncomputable def rootImageRadius (b : Bad (nativePlaceSelection T)) : NNReal :=
  Finset.univ.sup (fun j : ThetaLabel (l := l) =>
    ⟨‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
      rootNormedExtension T b)‖, norm_nonneg _⟩)

/-- Actual coordinatewise minimal product image hull. -/
def rootExtensionProductImageHull :
    Set (RootExtensionProductCarrier T) :=
  Set.pi Set.univ (fun b =>
    Metric.closedBall (0 : rootNormedExtension T b)
      ((rootImageRadius T b : NNReal) : Real))

/-- Each root image point lies in the coordinatewise ball. -/
theorem rootImageRadius_ge (b : Bad (nativePlaceSelection T))
    (j : ThetaLabel (l := l)) :
    ‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
      rootNormedExtension T b)‖ ≤ (rootImageRadius T b : Real) := by
  have hle : (⟨‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
      rootNormedExtension T b)‖, norm_nonneg _⟩ : NNReal) ≤ rootImageRadius T b := by
    unfold rootImageRadius
    exact Finset.le_sup (α := NNReal) (β := ThetaLabel (l := l)) (s := Finset.univ)
      (f := fun j : ThetaLabel (l := l) =>
        (⟨‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
          rootNormedExtension T b)‖, norm_nonneg _⟩ : NNReal))
      (b := j) (Finset.mem_univ j)
  exact_mod_cast hle

/-- Root theta image is contained in the actual image hull. -/
theorem rootExtensionProductThetaImageSet_subset_imageHull :
    rootExtensionProductThetaImageSet T ⊆ rootExtensionProductImageHull T := by
  rintro x ⟨j, rfl⟩
  intro b _
  rw [Metric.mem_closedBall]
  simpa [rootExtensionProductThetaImage, dist_eq_norm] using
    rootImageRadius_ge (T := T) b j

/-- The minimal image hull is contained in the full product unit ball. -/
theorem rootExtensionProductImageHull_subset_unitBall
    (hq : RootQUnitNormLeOne (T := T)) :
    rootExtensionProductImageHull T ⊆ rootExtensionProductUnitBall T := by
  intro x hx b hb
  have hx' : (x b : rootNormedExtension T b) ∈
      Metric.closedBall (0 : rootNormedExtension T b)
        ((rootImageRadius T b : NNReal) : Real) := hx b hb
  rw [Metric.mem_closedBall] at hx'
  change (x b : rootNormedExtension T b) ∈ rootExtensionUnitBall T b
  unfold rootExtensionUnitBall
  rw [Metric.mem_closedBall]
  have hbound : (rootImageRadius T b : Real) ≤ 1 := by
    unfold rootImageRadius
    have hle : ∀ j : ThetaLabel (l := l),
        (⟨‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
          rootNormedExtension T b)‖, norm_nonneg _⟩ : NNReal) ≤ 1 := by
      intro j
      exact_mod_cast rootExtensionProductNormBound_of_qUnit (T := T) hq j b
    change (Finset.univ.sup (fun j : ThetaLabel (l := l) =>
      (⟨‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
        rootNormedExtension T b)‖, norm_nonneg _⟩ : NNReal)) : NNReal) ≤ 1
    exact_mod_cast Finset.sup_le (fun j _ => hle j)
  exact le_trans (by simpa [dist_eq_norm] using hx') hbound

/-- The root element is nonzero. -/
theorem rootNormedElement_ne_zero : (rootNormedElement T b : rootNormedAmbient T b) ≠ 0 := by
  simpa [rootNormedElement] using Units.ne_zero (sourceRoot T b)

/-- The root image radius is positive (the label-1 image is a nonzero unit). -/
theorem rootImageRadius_pos : 0 < rootImageRadius T b := by
  let j1 : ThetaLabel (l := l) := ⟨oneLabel l, by rw [oneLabel_val]; norm_num⟩
  have hge : (⟨‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j1) :
      rootNormedExtension T b)‖, norm_nonneg _⟩ : NNReal) ≤ rootImageRadius T b := by
    unfold rootImageRadius
    exact Finset.le_sup (α := NNReal) (β := ThetaLabel (l := l))
      (s := Finset.univ)
      (f := fun j : ThetaLabel (l := l) =>
        (⟨‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
          rootNormedExtension T b)‖, norm_nonneg _⟩ : NNReal))
      (b := j1) (Finset.mem_univ j1)
  have hnormpos : 0 < ‖(rootNormedThetaValueInL T b
      (thetaLabelToSigned (l := l) j1) : rootNormedExtension T b)‖ := by
    rw [norm_pos_iff]
    intro hzero
    have hval : (rootNormedElement T b) ^
        (gaussExponent (thetaLabelToSigned (l := l) j1).1) = 0 := by
      simpa [rootNormedThetaValueInL, rootNormedThetaValue] using congrArg Subtype.val hzero
    exact zpow_ne_zero _ (rootNormedElement_ne_zero (T := T) (b := b)) hval
  exact lt_of_lt_of_le (by exact_mod_cast hnormpos) hge

/-- Local closed ball of positive radius has positive Haar measure. -/
theorem rootExtensionClosedBall_measure_pos (r : Real) (hr : 0 < r) :
    0 < rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b) r) := by
  have hopen : 0 < rootExtensionHaar T b (Metric.ball (0 : rootNormedExtension T b) r) :=
    Metric.measure_ball_pos (rootExtensionHaar T b) (0 : rootNormedExtension T b) hr
  exact lt_of_lt_of_le hopen (measure_mono (Metric.ball_subset_closedBall))

/-- Local closed ball has finite Haar measure. -/
theorem rootExtensionClosedBall_measure_lt_top (r : Real) :
    rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b) r) < ⊤ :=
  (isCompact_closedBall (0 : rootNormedExtension T b) r).measure_lt_top

/-- Product image hull has positive finite Haar measure. -/
theorem rootExtensionProductImageHull_measure_pos_lt_top :
    0 < rootExtensionProductHaar T (rootExtensionProductImageHull T) ∧
      rootExtensionProductHaar T (rootExtensionProductImageHull T) < ⊤ := by
  unfold rootExtensionProductHaar rootExtensionProductImageHull
  rw [Measure.pi_pi]
  constructor
  · rw [pos_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun b _ => ne_of_gt
      (rootExtensionClosedBall_measure_pos (T := T) (b := b)
        ((rootImageRadius T b : NNReal) : Real)
        (by exact_mod_cast rootImageRadius_pos (T := T) (b := b))))
  · apply ENNReal.prod_lt_top
    intro b _
    exact rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _

/-- Actual normalized log of the coordinatewise minimal image hull, relative to
the full product unit ball. -/
noncomputable def rootExtensionProductImageHullLog : Real :=
  rootExtensionProductNormalizedLog T (rootExtensionProductImageHull T)

/-- Definitional log-ratio form of the actual image hull log. -/
theorem rootExtensionProductImageHullLog_eq :
    rootExtensionProductImageHullLog T =
      Real.log (rootExtensionProductHaar T (rootExtensionProductImageHull T)).toReal -
        Real.log (rootExtensionProductHaar T (rootExtensionProductUnitBall T)).toReal :=
  rfl

end LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual

end