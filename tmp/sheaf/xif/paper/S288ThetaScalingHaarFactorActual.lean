import tmp.sheaf.xif.paper.S278HaarFactorConjugacyActual
import tmp.sheaf.xif.paper.S264CommonHaarScalarComputationActual

/-! # S288: thetaScalingHaarFactor computation on the unit ball

The block Haar scaling factor on blockUnitBall equals the ratio of the pushed
block Haar (which is rootNormedHaar by S264) on the L-scaled root unit ball by
the root unit ball.  The distribution-character formula gives rootHaarFactor.

No inequality/no fake factor/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S288ThetaScalingHaarFactorActual

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
open LeanFormal.IUT.XiFPaper.RootTensorHaarIsometryActual
open LeanFormal.IUT.XiFPaper.S255CommonHaarOnLActual
open LeanFormal.IUT.XiFPaper.S264CommonHaarScalarComputationActual
open LeanFormal.IUT.XiFPaper.S278HaarFactorConjugacyActual
open MeasureTheory
open scoped Pointwise

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- rootNormedUnitBall is the root extension unit ball. -/
theorem rootNormedUnitBall_eq_rootExtensionUnitBall :
    rootNormedUnitBall T b = rootExtensionUnitBall T b := rfl

/-- The pushed block Haar is rootNormedHaar. -/
theorem blockHaar_map_eq_rootNormedHaar :
    (blockHaar T b).map (blockLinearIsometryEquiv T b) =
      rootNormedHaar T b := by
  have h := commonHaarOnL_eq_rootNormedHaar (T := T) (b := b)
  unfold commonHaarOnL at h
  simpa using h

/-- thetaScalingHaarFactor equals rootHaarFactor, computed via the unit ball. -/
theorem thetaScalingHaarFactor_eq_rootHaarFactor
    (lam : (rootNormedExtension T b)ˣ) :
    (thetaScalingHaarFactor (T := T) (b := b)
      (lam : rootNormedExtension T b) (Units.ne_zero lam) : ENNReal) =
      rootHaarFactor T b lam := by
  let e := blockLinearIsometryEquiv T b
  let Tlam := blockScalingContinuousAddEquiv (T := T) (b := b)
    (lam : rootNormedExtension T b) (Units.ne_zero lam)
  have hspec := thetaScalingHaarFactor_spec (T := T) (b := b)
    (lam : rootNormedExtension T b) (Units.ne_zero lam)
    (S := blockUnitBall T b)
    (by simpa [blockUnitBall, blockUnitBallPositive] using
      (measurableSet_closedBall (x := (0 : rootTensorBlock T b)) (ε := 1)))
    (by simpa [blockUnitBall, blockUnitBallPositive] using
      (blockUnitBallPositive T b).isCompact)
  have hblock : blockHaar T b (Tlam '' blockUnitBall T b) =
      (thetaScalingHaarFactor (T := T) (b := b)
        (lam : rootNormedExtension T b) (Units.ne_zero lam) : ENNReal) := by
    simpa [Tlam, blockUnitBall_measure] using hspec
  have hmeas : MeasurableSet (e '' (Tlam '' blockUnitBall T b)) := by
    rw [image_blockScaling_unitBall]
    exact ((isCompact_closedBall (0 : rootNormedExtension T b) 1).image
      (continuous_const.mul continuous_id)).measurableSet
  have hmap := congrArg (fun μ : Measure (rootNormedExtension T b) =>
    μ (e '' (Tlam '' blockUnitBall T b))) (blockHaar_map_eq_rootNormedHaar (T := T) (b := b))
  rw [Measure.map_apply e.continuous.measurable hmeas] at hmap
  have hpre : e ⁻¹' (e '' (Tlam '' blockUnitBall T b)) =
      Tlam '' blockUnitBall T b :=
    Set.preimage_image_eq _ e.injective
  rw [hpre] at hmap
  rw [image_blockScaling_unitBall] at hmap
  have hden : rootNormedHaar T b (rootExtensionUnitBall T b) ≠ 0 := by
    rw [← rootNormedUnitBall_eq_rootExtensionUnitBall]
    rw [rootNormedUnitBall_measure]
    norm_num
  have htop : rootNormedHaar T b (rootExtensionUnitBall T b) ≠ ⊤ := by
    rw [← rootNormedUnitBall_eq_rootExtensionUnitBall]
    rw [rootNormedUnitBall_measure]
    exact ENNReal.one_ne_top
  have hchar := distribHaarChar_eq_div
    (μ := rootNormedHaar T b) (s := rootExtensionUnitBall T b)
    hden htop lam
  change rootHaarFactor T b lam =
    rootNormedHaar T b ((lam : rootNormedExtension T b) • rootExtensionUnitBall T b) /
      rootNormedHaar T b (rootExtensionUnitBall T b) at hchar
  rw [← hblock]
  calc
    blockHaar T b (Tlam '' blockUnitBall T b) =
        rootNormedHaar T b
          ((lam : rootNormedExtension T b) • rootExtensionUnitBall T b) := hmap
    _ = rootNormedHaar T b
          ((lam : rootNormedExtension T b) • rootExtensionUnitBall T b) /
        rootNormedHaar T b (rootExtensionUnitBall T b) := by
      rw [← rootNormedUnitBall_eq_rootExtensionUnitBall]
      rw [rootNormedUnitBall_measure]
      simp
    _ = rootHaarFactor T b lam := hchar.symm

end LeanFormal.IUT.XiFPaper.S288ThetaScalingHaarFactorActual

end
