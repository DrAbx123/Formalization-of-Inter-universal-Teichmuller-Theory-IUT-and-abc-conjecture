import tmp.sheaf.xif.paper.S255CommonHaarOnLActual

/-! # S264: computation of commonHaarScalarFactor

The continuous linear isometry maps blockUnitBall onto rootNormedUnitBall.
Hence the pushed block Haar of the L unit ball is 1, equal to the
rootNormedHaar unit ball mass 1.  Haar uniqueness then gives actual scalar 1 and
commonHaarOnL = rootNormedHaar.

No inequality/no fake Haar/scalar/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S264CommonHaarScalarComputationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.RootTensorThetaHullActual
open LeanFormal.IUT.XiFPaper.S255CommonHaarOnLActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The continuous linear isometry maps the tensor unit ball onto the L unit
ball. -/
theorem blockLinearIsometryEquiv_image_blockUnitBall :
    (blockLinearIsometryEquiv T b) '' blockUnitBall T b =
      rootNormedUnitBall T b := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ‖x‖ ≤ 1 := by
      simpa [blockUnitBall, blockUnitBallPositive] using hx
    simpa [rootNormedUnitBall, rootNormedUnitBallPositive,
      LinearIsometryEquiv.norm_map] using hx'
  · intro hy
    refine ⟨(blockLinearIsometryEquiv T b).symm y, ?_,
      (blockLinearIsometryEquiv T b).apply_symm_apply y⟩
    have hy' : ‖y‖ ≤ 1 := by
      simpa [rootNormedUnitBall, rootNormedUnitBallPositive] using hy
    simpa [blockUnitBall, blockUnitBallPositive,
      LinearIsometryEquiv.norm_map] using hy'

/-- The pushed block Haar assigns mass 1 to the L unit ball. -/
theorem commonHaarOnL_unitBall :
    commonHaarOnL T b (rootNormedUnitBall T b) = 1 := by
  unfold commonHaarOnL
  rw [Measure.map_apply]
  · rw [← blockLinearIsometryEquiv_image_blockUnitBall]
    have hpre : ⇑(blockLinearIsometryEquiv T b) ⁻¹'
        (⇑(blockLinearIsometryEquiv T b) '' blockUnitBall T b) =
        blockUnitBall T b :=
      Set.preimage_image_eq (blockUnitBall T b)
        (blockLinearIsometryEquiv T b).injective
    change (blockHaar T b) (⇑(blockLinearIsometryEquiv T b) ⁻¹'
      (⇑(blockLinearIsometryEquiv T b) '' blockUnitBall T b)) = 1
    rw [hpre]
    exact blockUnitBall_measure T b
  · exact (blockLinearIsometryEquiv T b).toContinuousLinearEquiv.continuous.measurable
  · simpa [rootNormedUnitBall, rootNormedUnitBallPositive] using
      (measurableSet_closedBall (x := (0 : rootNormedExtension T b)) (ε := 1))

/-- Haar uniqueness scalar is 1. -/
theorem commonHaarScalarFactor_eq_one :
    commonHaarScalarFactor T b = 1 := by
  have huniq := Measure.isAddLeftInvariant_eq_smul
    (commonHaarOnL T b) (rootNormedHaar T b)
  have hval := congrArg
    (fun μ : Measure (rootNormedExtension T b) =>
      μ (rootNormedUnitBall T b)) huniq
  change commonHaarOnL T b (rootNormedUnitBall T b) =
    (commonHaarScalarFactor T b • rootNormedHaar T b)
      (rootNormedUnitBall T b) at hval
  rw [Measure.smul_apply, smul_eq_mul, commonHaarOnL_unitBall,
    rootNormedUnitBall_measure] at hval
  simpa [eq_comm] using hval

/-- Hence commonHaarOnL is exactly rootNormedHaar. -/
theorem commonHaarOnL_eq_rootNormedHaar :
    commonHaarOnL T b = rootNormedHaar T b := by
  have huniq := Measure.isAddLeftInvariant_eq_smul
    (commonHaarOnL T b) (rootNormedHaar T b)
  change commonHaarOnL T b =
    commonHaarScalarFactor T b • rootNormedHaar T b at huniq
  rw [commonHaarScalarFactor_eq_one] at huniq
  simpa using huniq

end LeanFormal.IUT.XiFPaper.S264CommonHaarScalarComputationActual

end
