import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Sets.Compacts

/-! # Actual additive Haar on L and exact tensor-lift gap

L is finite-dimensional over the complete Qp field K, hence proper. Its closed
unit ball is a TopologicalSpace.PositiveCompacts for the additive group L.
Mathlib additive Haar is available on L; the unit ball has Haar measure 1
(positive/finite), and the normalized log is actual.

The actual root theta image set/hull and their Haar measure/normalized log in L
are constructed. Lifting this Haar to the actual tensor block over L is
recorded as the exact missing normed-group/measurable API; no tensor Haar is
fabricated.

No fake tensor norm or Haar. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual

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

/-- Measurable structure on L. -/
noncomputable instance rootNormedExtensionMeasurableSpaceHaar :
    MeasurableSpace (rootNormedExtension T b) :=
  borel (rootNormedExtension T b)

/-- L is proper (finite-dimensional over Qp). -/
noncomputable instance rootNormedExtensionProperSpace :
    ProperSpace (rootNormedExtension T b) := by
  haveI : FiniteDimensional (rootBase T b) (rootNormedExtension T b) :=
    rootNormedExtensionFiniteDimensional T b
  haveI : ProperSpace (rootBase T b) := inferInstance
  exact FiniteDimensional.proper (rootBase T b) (rootNormedExtension T b)

/-- Borel structure on L. -/
noncomputable instance rootNormedExtensionBorelSpaceHaar :
    BorelSpace (rootNormedExtension T b) := ⟨rfl⟩

/-- The actual positive compact unit ball for the additive group L. -/
noncomputable def rootNormedUnitBallPositive :
    TopologicalSpace.PositiveCompacts (rootNormedExtension T b) where
  carrier := Metric.closedBall (0 : rootNormedExtension T b) 1
  isCompact' := by
    simpa using (ProperSpace.isCompact_closedBall
      (0 : rootNormedExtension T b) 1)
  interior_nonempty' := by
    refine ⟨0, ?_⟩
    rw [mem_interior_iff_mem_nhds]
    exact Metric.mem_nhds_iff.mpr ⟨1, by norm_num, by
      intro y hy
      exact Metric.ball_subset_closedBall hy⟩

/-- The additive unit ball in L. -/
noncomputable def rootNormedUnitBall : Set (rootNormedExtension T b) :=
  (rootNormedUnitBallPositive T b : Set (rootNormedExtension T b))

/-- Actual additive Haar measure on L. -/
noncomputable def rootNormedHaar : Measure (rootNormedExtension T b) :=
  Measure.addHaarMeasure (rootNormedUnitBallPositive T b)

/-- The unit ball has Haar measure 1. -/
theorem rootNormedUnitBall_measure :
    rootNormedHaar T b (rootNormedUnitBall T b) = 1 := by
  unfold rootNormedHaar rootNormedUnitBall
  exact Measure.addHaarMeasure_self (K₀ := rootNormedUnitBallPositive T b)

theorem rootNormedUnitBall_measure_pos :
    0 < rootNormedHaar T b (rootNormedUnitBall T b) := by
  rw [rootNormedUnitBall_measure]
  norm_num

theorem rootNormedUnitBall_measure_lt_top :
    rootNormedHaar T b (rootNormedUnitBall T b) < ⊤ := by
  rw [rootNormedUnitBall_measure]
  exact ENNReal.one_lt_top

/-- Actual normalized log on L. -/
noncomputable def rootNormedHaarLog : Real :=
  Real.log (rootNormedHaar T b (rootNormedUnitBall T b)).toReal

theorem rootNormedHaarLog_eq_zero : rootNormedHaarLog T b = 0 := by
  unfold rootNormedHaarLog
  rw [rootNormedUnitBall_measure]
  norm_num

/-- Actual root theta image set in L. -/
noncomputable def rootNormedThetaImageSet : Set (rootNormedExtension T b) :=
  Set.range (rootNormedThetaValueInL T b)

/-- Actual root theta image hull in L. -/
noncomputable def rootNormedThetaHull : Set (rootNormedExtension T b) :=
  closure (rootNormedThetaImageSet T b)

/-- Haar measure of the root theta image hull. -/
noncomputable def rootNormedThetaHullMeasure : ENNReal :=
  rootNormedHaar T b (rootNormedThetaHull T b)

/-- Normalized log of the root theta image hull. -/
noncomputable def rootNormedThetaHullLog : Real :=
  Real.log (rootNormedThetaHullMeasure T b).toReal

/-- Exact missing lift of L-Haar to the tensor block over L. -/
def RootTensorHaarLiftAPIRequired : Prop :=
  Nonempty (NormedAddCommGroup (rootTensorBlock T b)) ∧
    Nonempty (MeasurableSpace (rootTensorBlock T b))

/-- Actual L-Haar/root-theta data. -/
structure RootNormedHaarData where
  haar : Measure (rootNormedExtension T b)
  haar_eq : haar = rootNormedHaar T b
  unitBall : Set (rootNormedExtension T b)
  unitBall_eq : unitBall = rootNormedUnitBall T b
  unitBall_measure : haar unitBall = 1
  normalizedLog : Real
  normalizedLog_eq : normalizedLog = rootNormedHaarLog T b
  thetaHull : Set (rootNormedExtension T b)
  thetaHull_eq : thetaHull = rootNormedThetaHull T b
  thetaHullMeasure : ENNReal
  thetaHullMeasure_eq : thetaHullMeasure = rootNormedThetaHullMeasure T b
  thetaHullLog : Real
  thetaHullLog_eq : thetaHullLog = rootNormedThetaHullLog T b

/-- The actual L-Haar data constructor. -/
noncomputable def rootNormedHaarData : RootNormedHaarData T b where
  haar := rootNormedHaar T b
  haar_eq := rfl
  unitBall := rootNormedUnitBall T b
  unitBall_eq := rfl
  unitBall_measure := rootNormedUnitBall_measure T b
  normalizedLog := rootNormedHaarLog T b
  normalizedLog_eq := rfl
  thetaHull := rootNormedThetaHull T b
  thetaHull_eq := rfl
  thetaHullMeasure := rootNormedThetaHullMeasure T b
  thetaHullMeasure_eq := rfl
  thetaHullLog := rootNormedThetaHullLog T b
  thetaHullLog_eq := rfl

end LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual

end