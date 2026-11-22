import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootTensorHaarActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import Mathlib.NumberTheory.Padics.ProperSpace

/-! # Actual Haar on the root tensor block over L

The FinitePadicTensor instances are used with explicit letI for the normed
additive group, Qp normed space and finite-dimensional structure on L.
Then the native tensor block over L gets NormedAddCommGroup, ProperSpace and
MeasurableSpace/BorelSpace, the closed unit ball is a PositiveCompacts, and
Measure.addHaarMeasure is the actual Haar.  The unit ball has Haar measure 1,
positive and finite.  The root theta image hull measure/log are defined from
this actual Haar.

No fake Haar. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperRootTensorHaarFinitePadicActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual
open LeanFormal.IUT.LocalFieldPadicTensor
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Normed additive group on the native tensor block over L. -/
noncomputable instance rootTensorBlockNormedAddCommGroup :
    NormedAddCommGroup (rootTensorBlock T b) := by
  letI : NormedAddCommGroup (rootNormedExtension T b) := inferInstance
  letI : NormedSpace ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    rootNormedExtensionNormedSpaceQp T b
  letI : FiniteDimensional ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    rootNormedExtensionFiniteDimensionalQp T b
  haveI : ∀ _ : Unit, NormedAddCommGroup (rootNormedExtension T b) := fun _ => inferInstance
  haveI : ∀ _ : Unit, NormedSpace ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    fun _ => rootNormedExtensionNormedSpaceQp T b
  haveI : ∀ _ : Unit, FiniteDimensional ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    fun _ => rootNormedExtensionFiniteDimensionalQp T b
  letI : Fintype Unit := inferInstance
  exact @finitePadicTensorNormedAddCommGroup (qVFamTensorP T b) (inferInstance : Fact (Nat.Prime (qVFamTensorP T b))) Unit inferInstance (fun _ : Unit => rootNormedExtension T b) (fun _ : Unit => (inferInstance : NormedAddCommGroup (rootNormedExtension T b))) (fun _ : Unit => rootNormedExtensionNormedSpaceQp T b) (fun _ : Unit => rootNormedExtensionFiniteDimensionalQp T b)

/-- Topological space on the tensor block. -/
noncomputable instance rootTensorBlockTopologicalSpace :
    TopologicalSpace (rootTensorBlock T b) :=
  inferInstance

/-- Proper-space instance on the tensor block. -/
noncomputable instance rootTensorBlockProperSpace :
    ProperSpace (rootTensorBlock T b) := by
  letI : NormedAddCommGroup (rootNormedExtension T b) := inferInstance
  letI : NormedSpace ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    rootNormedExtensionNormedSpaceQp T b
  letI : FiniteDimensional ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    rootNormedExtensionFiniteDimensionalQp T b
  haveI : ∀ _ : Unit, NormedAddCommGroup (rootNormedExtension T b) := fun _ => inferInstance
  haveI : ∀ _ : Unit, NormedSpace ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    fun _ => rootNormedExtensionNormedSpaceQp T b
  haveI : ∀ _ : Unit, FiniteDimensional ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
    fun _ => rootNormedExtensionFiniteDimensionalQp T b
  letI : Fintype Unit := inferInstance
  exact @finitePadicTensorProperSpace (qVFamTensorP T b) (inferInstance : Fact (Nat.Prime (qVFamTensorP T b))) Unit inferInstance (fun _ : Unit => rootNormedExtension T b) (fun _ : Unit => (inferInstance : NormedAddCommGroup (rootNormedExtension T b))) (fun _ : Unit => rootNormedExtensionNormedSpaceQp T b) (fun _ : Unit => rootNormedExtensionFiniteDimensionalQp T b)

/-- Measurable structure on the tensor block. -/
noncomputable instance rootTensorBlockMeasurableSpace :
    MeasurableSpace (rootTensorBlock T b) :=
  borel (rootTensorBlock T b)

/-- Borel structure on the tensor block. -/
noncomputable instance rootTensorBlockBorelSpace :
    BorelSpace (rootTensorBlock T b) := ⟨rfl⟩

/-- The actual positive compact unit ball for the additive tensor block. -/
noncomputable def rootTensorUnitBallPositive :
    TopologicalSpace.PositiveCompacts (rootTensorBlock T b) where
  carrier := Metric.closedBall (0 : rootTensorBlock T b) 1
  isCompact' := by
    simpa using (ProperSpace.isCompact_closedBall (0 : rootTensorBlock T b) 1)
  interior_nonempty' := by
    refine ⟨0, ?_⟩
    rw [mem_interior_iff_mem_nhds]
    exact Metric.mem_nhds_iff.mpr ⟨1, by norm_num, by
      intro y hy
      exact Metric.ball_subset_closedBall hy⟩

/-- The actual unit ball in the tensor block. -/
noncomputable def rootTensorUnitBall : Set (rootTensorBlock T b) :=
  (rootTensorUnitBallPositive T b : Set (rootTensorBlock T b))

/-- Actual Haar measure on the root tensor block. -/
noncomputable def rootTensorHaar : Measure (rootTensorBlock T b) :=
  Measure.addHaarMeasure (rootTensorUnitBallPositive T b)

/-- The root tensor unit ball has Haar measure 1. -/
theorem rootTensorUnitBall_measure :
    rootTensorHaar T b (rootTensorUnitBall T b) = 1 := by
  unfold rootTensorHaar rootTensorUnitBall
  exact Measure.addHaarMeasure_self (K₀ := rootTensorUnitBallPositive T b)

theorem rootTensorUnitBall_measure_pos :
    0 < rootTensorHaar T b (rootTensorUnitBall T b) := by
  rw [rootTensorUnitBall_measure]
  norm_num

theorem rootTensorUnitBall_measure_lt_top :
    rootTensorHaar T b (rootTensorUnitBall T b) < ⊤ := by
  rw [rootTensorUnitBall_measure]
  exact ENNReal.one_lt_top

/-- Actual normalized log on the tensor block. -/
noncomputable def rootTensorHaarLog : Real :=
  Real.log (rootTensorHaar T b (rootTensorUnitBall T b)).toReal

theorem rootTensorHaarLog_eq_zero : rootTensorHaarLog T b = 0 := by
  unfold rootTensorHaarLog
  rw [rootTensorUnitBall_measure]
  norm_num

/-- Actual theta image set in the tensor block. -/
noncomputable def rootTensorThetaImageSet : Set (rootTensorBlock T b) :=
  Set.range (rootTensorThetaImage T b)

/-- Actual theta image hull in the tensor block. -/
noncomputable def rootTensorThetaHull : Set (rootTensorBlock T b) :=
  closure (rootTensorThetaImageSet T b)

/-- Haar measure of the actual theta image hull. -/
noncomputable def rootTensorThetaHullMeasure : ENNReal :=
  rootTensorHaar T b (rootTensorThetaHull T b)

/-- Normalized log of the actual theta image hull. -/
noncomputable def rootTensorThetaHullLog : Real :=
  Real.log (rootTensorThetaHullMeasure T b).toReal

/-- Actual tensor Haar/theta data. -/
structure RootTensorHaarData where
  haar : Measure (rootTensorBlock T b)
  haar_eq : haar = rootTensorHaar T b
  unitBall : Set (rootTensorBlock T b)
  unitBall_eq : unitBall = rootTensorUnitBall T b
  unitBall_measure : haar unitBall = 1
  normalizedLog : Real
  normalizedLog_eq : normalizedLog = rootTensorHaarLog T b
  thetaHull : Set (rootTensorBlock T b)
  thetaHull_eq : thetaHull = rootTensorThetaHull T b
  thetaHullMeasure : ENNReal
  thetaHullMeasure_eq : thetaHullMeasure = rootTensorThetaHullMeasure T b
  thetaHullLog : Real
  thetaHullLog_eq : thetaHullLog = rootTensorThetaHullLog T b

noncomputable def rootTensorHaarData : RootTensorHaarData T b where
  haar := rootTensorHaar T b
  haar_eq := rfl
  unitBall := rootTensorUnitBall T b
  unitBall_eq := rfl
  unitBall_measure := rootTensorUnitBall_measure T b
  normalizedLog := rootTensorHaarLog T b
  normalizedLog_eq := rfl
  thetaHull := rootTensorThetaHull T b
  thetaHull_eq := rfl
  thetaHullMeasure := rootTensorThetaHullMeasure T b
  thetaHullMeasure_eq := rfl
  thetaHullLog := rootTensorThetaHullLog T b
  thetaHullLog_eq := rfl

end LeanFormal.IUT.XiFPaper.PaperRootTensorHaarFinitePadicActual

end