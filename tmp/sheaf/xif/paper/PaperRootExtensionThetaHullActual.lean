import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionNormBoundActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootActual
import tmp.sheaf.xif.paper.SignedLabelOneActual

/-! # Actual root extension product Theta hull and normalized mu_log -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullActual

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
variable [MeasurableSpace (RootExtensionProductCarrier T)]

/-- Actual product Theta hull: the product of the local closed unit balls. -/
def rootExtensionProductThetaHull :
    Set (RootExtensionProductCarrier T) :=
  rootExtensionProductUnitBall T

/-- Actual normalized mu_log of the product hull, relative to the same unit ball. -/
noncomputable def rootExtensionProductThetaHullLog : Real :=
  rootExtensionProductNormalizedLog T (rootExtensionProductThetaHull T)

/-- Hull log is zero. -/
theorem rootExtensionProductThetaHullLog_eq_zero :
    rootExtensionProductThetaHullLog T = 0 :=
  rootExtensionProductNormalizedLog_unitBall T

/-- Hull Haar measure is positive finite. -/
theorem rootExtensionProductThetaHull_measure_pos_lt_top :
    0 < rootExtensionProductHaar T (rootExtensionProductThetaHull T) ∧
      rootExtensionProductHaar T (rootExtensionProductThetaHull T) < ⊤ :=
  rootExtensionProductHaar_unitBall_pos_lt_top T

/-- Root theta image is contained in the actual product hull. -/
theorem rootExtensionProductThetaImageSet_subset_hull
    (hq : RootQUnitNormLeOne (T := T)) :
    rootExtensionProductThetaImageSet T ⊆ rootExtensionProductThetaHull T :=
  rootExtensionProductThetaImageSet_subset_unitBall_of_qUnit (T := T) hq

/-- Actual Dirac image-count measure on the root extension product carrier. -/
noncomputable def rootExtensionProductImageMeasure :
    Measure (RootExtensionProductCarrier T) :=
  ∑ j : ThetaLabel (l := l),
    Measure.dirac
      (rootExtensionProductThetaImage T (thetaLabelToSigned (l := l) j))

/-- The image-count measure of the hull is the number of ThetaLabels. -/
theorem rootExtensionProductImageMeasure_hull
    (hq : RootQUnitNormLeOne (T := T)) :
    rootExtensionProductImageMeasure T (rootExtensionProductThetaHull T) =
      (Fintype.card (ThetaLabel (l := l)) : ENNReal) := by
  unfold rootExtensionProductImageMeasure rootExtensionProductThetaHull
  rw [Measure.finsetSum_apply]
  rw [show (Fintype.card (ThetaLabel (l := l)) : ENNReal) =
    ∑ _ : ThetaLabel (l := l), (1 : ENNReal) by simp]
  apply Finset.sum_congr rfl
  intro j _
  have hmem : rootExtensionProductThetaImage T (thetaLabelToSigned (l := l) j) ∈
      rootExtensionProductUnitBall T :=
    rootExtensionProductThetaImageSet_subset_unitBall_of_qUnit (T := T) hq
      ⟨thetaLabelToSigned (l := l) j, rfl⟩
  rw [Measure.dirac_apply_of_mem hmem]

/-- The image-count measure is positive finite on the hull. -/
theorem rootExtensionProductImageMeasure_hull_pos_lt_top
    (hq : RootQUnitNormLeOne (T := T)) :
    0 < rootExtensionProductImageMeasure T (rootExtensionProductThetaHull T) ∧
      rootExtensionProductImageMeasure T (rootExtensionProductThetaHull T) < ⊤ := by
  rw [rootExtensionProductImageMeasure_hull (T := T) hq]
  constructor
  · haveI : Nonempty (ThetaLabel (l := l)) :=
      ⟨⟨oneLabel l, by rw [oneLabel_val]; norm_num⟩⟩
    exact_mod_cast Fintype.card_pos
  · exact ENNReal.natCast_lt_top _

end LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullActual

end