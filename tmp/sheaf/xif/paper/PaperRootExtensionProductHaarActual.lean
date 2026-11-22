import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootActual

/-! # Actual finite-product Haar on the root extension family -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Finite product carrier of the root extension fields. -/
abbrev RootExtensionProductCarrier : Type :=
  (b : Bad (nativePlaceSelection T)) → rootNormedExtension T b

/-- Actual finite-product Haar measure. -/
noncomputable def rootExtensionProductHaar :
    Measure (RootExtensionProductCarrier T) :=
  Measure.pi (fun b => rootExtensionHaar T b)

/-- Product unit ball: one closed unit ball in each finite root extension. -/
def rootExtensionProductUnitBall :
    Set (RootExtensionProductCarrier T) :=
  Set.pi Set.univ (fun b => rootExtensionUnitBall T b)

/-- Product Haar of the product unit ball is the product of local unit-ball
masses. -/
theorem rootExtensionProductHaar_unitBall :
    rootExtensionProductHaar T (rootExtensionProductUnitBall T) =
      ∏ b : Bad (nativePlaceSelection T),
        rootExtensionHaar T b (rootExtensionUnitBall T b) := by
  unfold rootExtensionProductHaar rootExtensionProductUnitBall
  rw [Measure.pi_pi]

/-- Product unit ball has positive finite Haar measure. -/
theorem rootExtensionProductHaar_unitBall_pos_lt_top :
    0 < rootExtensionProductHaar T (rootExtensionProductUnitBall T) ∧
      rootExtensionProductHaar T (rootExtensionProductUnitBall T) < ⊤ := by
  rw [rootExtensionProductHaar_unitBall]
  constructor
  · rw [pos_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun b _ =>
      ne_of_gt (rootExtensionUnitBall_measure_pos T b))
  · apply ENNReal.prod_lt_top
    intro b _
    exact rootExtensionUnitBall_measure_lt_top T b

/-- Actual root theta image in the finite product carrier. -/
noncomputable def rootExtensionProductThetaImage
    (j : ThetaLabel (l := l)) : RootExtensionProductCarrier T :=
  fun b => rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j)

/-- Actual root theta image set in the finite product carrier. -/
noncomputable def rootExtensionProductThetaImageSet :
    Set (RootExtensionProductCarrier T) :=
  Set.range (rootExtensionProductThetaImage T)

/-- Exact norm condition for the root image to lie in the product unit ball. -/
def RootExtensionProductNormBound : Prop :=
  ∀ (j : ThetaLabel (l := l)) (b : Bad (nativePlaceSelection T)),
    ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖ ≤ 1

/-- Under the exact root norm bound, the root theta image lies in the product
unit ball. -/
theorem rootExtensionProductThetaImageSet_subset_unitBall
    (hroot : RootExtensionProductNormBound T) :
    rootExtensionProductThetaImageSet T ⊆ rootExtensionProductUnitBall T := by
  rintro x ⟨j, rfl⟩
  intro b _
  unfold rootExtensionUnitBall
  rw [Metric.mem_closedBall]
  simpa [rootExtensionProductThetaImage, thetaLabelToSigned, dist_eq_norm] using hroot j b

/-- Actual normalized product log of a product measurable set, relative to the
product unit ball. -/
noncomputable def rootExtensionProductNormalizedLog
    (S : Set (RootExtensionProductCarrier T)) : Real :=
  Real.log (rootExtensionProductHaar T S).toReal -
    Real.log (rootExtensionProductHaar T (rootExtensionProductUnitBall T)).toReal

/-- Normalized log of the unit ball itself is zero. -/
theorem rootExtensionProductNormalizedLog_unitBall :
    rootExtensionProductNormalizedLog T (rootExtensionProductUnitBall T) = 0 := by
  unfold rootExtensionProductNormalizedLog
  ring

end LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual

end