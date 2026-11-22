import tmp.sheaf.xif.paper.RootTensorThetaHullActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarFactorActual
import tmp.sheaf.xif.paper.PaperRootTensorHaarActual
import tmp.sheaf.xif.paper.S264CommonHaarScalarComputationActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.RootTensorHaarIsometryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarFactorActual
open LeanFormal.IUT.XiFPaper.RootTensorThetaHullActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.S255CommonHaarOnLActual
open LeanFormal.IUT.XiFPaper.S264CommonHaarScalarComputationActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The root extension unit ball as a positive compact. -/
noncomputable def rootExtensionUnitBallPositive :
    TopologicalSpace.PositiveCompacts (rootNormedExtension T b) where
  carrier := rootExtensionUnitBall T b
  isCompact' := by
    simpa [rootExtensionUnitBall] using
      (ProperSpace.isCompact_closedBall (0 : rootNormedExtension T b) 1)
  interior_nonempty' := by
    refine ⟨0, ?_⟩
    rw [mem_interior_iff_mem_nhds]
    simpa [rootExtensionUnitBall] using
      (Metric.closedBall_mem_nhds (0 : rootNormedExtension T b) zero_lt_one)

/-- The block unit ball maps exactly to the root extension unit ball. -/
theorem blockLinearIsometryEquiv_image_blockUnitBall :
    (blockLinearIsometryEquiv T b) '' blockUnitBall T b =
      rootExtensionUnitBall T b := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [blockUnitBall, blockUnitBallPositive, rootExtensionUnitBall,
      Metric.mem_closedBall, (blockLinearIsometryEquiv T b).norm_map x] using hx
  · intro hy
    refine ⟨(blockLinearIsometryEquiv T b).symm y, ?_, by simp⟩
    simpa [blockUnitBall, blockUnitBallPositive, rootExtensionUnitBall,
      Metric.mem_closedBall, (blockLinearIsometryEquiv T b).symm.norm_map y] using hy

/-- The block isometry as a continuous Qp-linear equivalence. -/
noncomputable def blockContinuousLinearEquiv :
    rootTensorBlock T b ≃L[ℚ_[(qVFamTensorP T b)]] (rootNormedExtension T b) :=
  (blockLinearIsometryEquiv T b).toContinuousLinearEquiv

/-- The isometry maps the block Haar to the normalized root Haar. -/
theorem blockHaar_map_eq_inv_smul_rootExtensionHaar :
    (blockHaar T b).map (blockContinuousLinearEquiv T b) =
      (rootExtensionHaar T b (rootExtensionUnitBall T b))⁻¹ •
        rootExtensionHaar T b := by
  let e := blockContinuousLinearEquiv T b
  haveI : MeasureTheory.Measure.IsAddHaarMeasure ((blockHaar T b).map e) :=
    e.isAddHaarMeasure_map (blockHaar T b)
  have hK : ((blockHaar T b).map e) (rootExtensionUnitBallPositive T b) = 1 := by
    change ((blockHaar T b).map e)
      (Metric.closedBall (0 : rootNormedExtension T b) 1) = 1
    rw [MeasureTheory.Measure.map_apply e.continuous.measurable
      measurableSet_closedBall]
    change (blockHaar T b) (e ⁻¹' rootExtensionUnitBall T b) = 1
    have hpre : e ⁻¹' rootExtensionUnitBall T b = blockUnitBall T b := by
      rw [← blockLinearIsometryEquiv_image_blockUnitBall (T := T) (b := b)]
      exact (Set.preimage_image_eq _ e.injective)
    rw [hpre]
    exact blockUnitBall_measure T b
  have huniq := MeasureTheory.Measure.addHaarMeasure_unique
    (μ := (blockHaar T b).map e) (rootExtensionUnitBallPositive T b)
  have huniqRoot := MeasureTheory.Measure.addHaarMeasure_unique
    (μ := rootExtensionHaar T b) (rootExtensionUnitBallPositive T b)
  have hroot' : rootExtensionHaar T b =
      (rootExtensionHaar T b) (rootExtensionUnitBall T b) •
        MeasureTheory.Measure.addHaarMeasure (rootExtensionUnitBallPositive T b) := by
    simpa [rootExtensionUnitBallPositive] using huniqRoot
  have hcval :
      (((rootExtensionHaar T b (rootExtensionUnitBall T b)) •
        MeasureTheory.Measure.addHaarMeasure (rootExtensionUnitBallPositive T b))
        (rootExtensionUnitBall T b)) =
      rootExtensionHaar T b (rootExtensionUnitBall T b) := by
    rw [MeasureTheory.Measure.smul_apply]
    have h1 : MeasureTheory.Measure.addHaarMeasure
        (rootExtensionUnitBallPositive T b) (rootExtensionUnitBall T b) = 1 := by
      simpa [rootExtensionUnitBallPositive] using
        (MeasureTheory.Measure.addHaarMeasure_self
          (K₀ := rootExtensionUnitBallPositive T b))
    rw [h1, smul_eq_mul, mul_one]
  have hc0 : rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0 :=
    ne_of_gt (rootExtensionUnitBall_measure_pos T b)
  have hctop : rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤ :=
    ne_of_lt (rootExtensionUnitBall_measure_lt_top T b)
  calc
    (blockHaar T b).map e = MeasureTheory.Measure.addHaarMeasure
        (rootExtensionUnitBallPositive T b) := by
      rw [huniq, hK, one_smul]
    _ = (rootExtensionHaar T b (rootExtensionUnitBall T b))⁻¹ •
          rootExtensionHaar T b := by
      rw [hroot']
      rw [hcval]
      rw [← smul_assoc, smul_eq_mul,
        ENNReal.inv_mul_cancel hc0 hctop, one_smul]

/-- S264: the pushed block Haar is exactly rootNormedHaar, so no extra scalar remains. -/
theorem blockHaar_map_eq_rootNormedHaar :
    (blockHaar T b).map (blockContinuousLinearEquiv T b) = rootNormedHaar T b := by
  simpa [blockContinuousLinearEquiv, S255CommonHaarOnLActual.commonHaarOnL]
    using (S264CommonHaarScalarComputationActual.commonHaarOnL_eq_rootNormedHaar
      (T := T) (b := b))

end LeanFormal.IUT.XiFPaper.RootTensorHaarIsometryActual
end
