import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootTensorHaarActual
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Group.Measure

/-! # Actual Haar on the root tensor block over L

The one-factor PiTensorProduct linear equivalence

  rootTensorBlock T b ≃ₗ[Qp] L

is actual (PiTensorProduct.subsingletonEquiv).  It is promoted to a
continuous linear equivalence in finite dimension; the actual Haar on L is
pushed forward along that equivalence.  The preimage unit ball has measure 1,
hence is positive/finite.  The root theta image hull and its Haar measure/log
are defined on the tensor block.

No fake Haar. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperRootTensorHaarLiftActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual one-factor linear equivalence block ≃ L. -/
noncomputable def rootTensorBlockLinearEquiv :
    rootTensorBlock T b ≃ₗ[ℚ_[(qVFamTensorP T b)]] (rootNormedExtension T b) :=
  PiTensorProduct.subsingletonEquiv (R := ℚ_[(qVFamTensorP T b)])
    (fun _ : Unit => rootNormedExtension T b) ()

/-- The actual continuous linear equivalence block ≃ L (finite dimension). -/
noncomputable def rootTensorBlockCLE :
    rootTensorBlock T b ≃L[ℚ_[(qVFamTensorP T b)]] (rootNormedExtension T b) :=
  (rootTensorBlockLinearEquiv T b).toContinuousLinearEquiv

/-- Actual Haar on the root tensor block: pushforward of the actual L-Haar. -/
noncomputable def rootTensorHaar : Measure (rootTensorBlock T b) :=
  (rootNormedHaar T b).map (rootTensorBlockCLE T b).symm

/-- The actual Haar is additive-Haar (image of Haar under a continuous linear
equivalence). -/
noncomputable instance rootTensorHaarIsAddHaar :
    Measure.IsAddHaarMeasure (rootTensorHaar T b) :=
  ContinuousLinearEquiv.isAddHaarMeasure_map (rootNormedHaar T b)
    (rootTensorBlockCLE T b).symm (rootTensorBlockCLE T b).symm.continuous
    (rootTensorBlockCLE T b).symm.toHomeomorph.surjective

/-- The actual unit ball in the root tensor block: preimage of the L unit ball. -/
noncomputable def rootTensorUnitBall : Set (rootTensorBlock T b) :=
  (rootTensorBlockCLE T b).symm ⁻¹' (rootNormedUnitBall T b)

/-- The root tensor unit ball has Haar measure 1 (actual). -/
theorem rootTensorUnitBall_measure :
    rootTensorHaar T b (rootTensorUnitBall T b) = 1 := by
  rw [rootTensorHaar, Measure.map_apply]
  · rw [rootNormedUnitBall_measure]
  · exact (rootTensorBlockCLE T b).symm.measurable measurableSet_rootNormedUnitBall
  · exact measurableSet_rootNormedUnitBall

theorem rootTensorUnitBall_measure_pos :
    0 < rootTensorHaar T b (rootTensorUnitBall T b) := by
  rw [rootTensorUnitBall_measure]
  norm_num

theorem rootTensorUnitBall_measure_lt_top :
    rootTensorHaar T b (rootTensorUnitBall T b) < ⊤ := by
  rw [rootTensorUnitBall_measure]
  exact ENNReal.one_lt_top

/-- Actual normalized log on the tensor block, normalized at the unit ball. -/
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

end LeanFormal.IUT.XiFPaper.PaperRootTensorHaarLiftActual

end