import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual

/-! # Actual Haar on the finite root extension L -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators Pointwise

namespace LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- L is proper over Qp, hence locally compact. -/
noncomputable instance rootExtensionProperSpace :
    ProperSpace (rootNormedExtension T b) := by
  letI : ProperSpace (rootBase T b) := inferInstance
  letI : NormedSpace (rootBase T b) (rootNormedExtension T b) := inferInstance
  letI : FiniteDimensional (rootBase T b) (rootNormedExtension T b) :=
    rootNormedExtensionFiniteDimensional (T := T) (b := b)
  exact FiniteDimensional.proper (𝕜 := rootBase T b) (E := rootNormedExtension T b)

/-- Actual additive Haar measure on the finite root extension L. -/
noncomputable def rootExtensionHaar : Measure (rootNormedExtension T b) :=
  Measure.addHaar

noncomputable instance rootExtensionHaarIsAddHaar :
    Measure.IsAddHaarMeasure (rootExtensionHaar T b) := by
  unfold rootExtensionHaar
  infer_instance

/-- The unit ball of L. -/
def rootExtensionUnitBall : Set (rootNormedExtension T b) :=
  Metric.closedBall (0 : rootNormedExtension T b) 1

/-- Unit ball has positive Haar measure. -/
theorem rootExtensionUnitBall_measure_pos :
    0 < rootExtensionHaar T b (rootExtensionUnitBall T b) := by
  unfold rootExtensionHaar rootExtensionUnitBall
  have hopen : 0 < Measure.addHaar (Metric.ball (0 : rootNormedExtension T b) 1) :=
    Metric.measure_ball_pos (Measure.addHaar) (0 : rootNormedExtension T b)
      (by norm_num : (0 : Real) < 1)
  exact lt_of_lt_of_le hopen
    (measure_mono (Metric.ball_subset_closedBall))

/-- Unit ball has finite Haar measure. -/
theorem rootExtensionUnitBall_measure_lt_top :
    rootExtensionHaar T b (rootExtensionUnitBall T b) < ⊤ := by
  unfold rootExtensionHaar rootExtensionUnitBall
  exact (isCompact_closedBall (0 : rootNormedExtension T b) 1).measure_lt_top

/-- Actual local Haar data on the finite root extension. -/
structure RootExtensionLocalHaarData where
  carrier : Type
  [measurableSpace : MeasurableSpace carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [addGroup : AddGroup carrier]
  [isTopologicalAddGroup : IsTopologicalAddGroup carrier]
  [locallyCompact : LocallyCompactSpace carrier]
  measure : Measure carrier
  [isAddHaar : Measure.IsAddHaarMeasure measure]
  unitBall : Set carrier
  unitBall_pos : 0 < measure unitBall
  unitBall_lt_top : measure unitBall < ⊤

/-- Actual local Haar data constructor for L. -/
noncomputable def rootExtensionLocalHaarData :
    RootExtensionLocalHaarData where
  carrier := rootNormedExtension T b
  measurableSpace := inferInstance
  topologicalSpace := inferInstance
  addGroup := inferInstance
  isTopologicalAddGroup := inferInstance
  locallyCompact := inferInstance
  measure := rootExtensionHaar T b
  isAddHaar := inferInstance
  unitBall := rootExtensionUnitBall T b
  unitBall_pos := rootExtensionUnitBall_measure_pos T b
  unitBall_lt_top := rootExtensionUnitBall_measure_lt_top T b

end LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual

end