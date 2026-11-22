import tmp.sheaf.xif.paper.RootTensorHaarIsometryActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarFactorActual

/-! # S278: partial conjugacy for block/root Haar factors

The isometry image of the scaled block unit ball is proved (conjugacy at the
set level).  The full scalar factor equality requires the measure-transport
calculation on that scaled set; that final equality is recorded as an exact
requirement, not faked.

No inequality/no fake factor/sorry/axiom/True/PUnit.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S278HaarFactorConjugacyActual

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
open MeasureTheory
open scoped Pointwise

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The isometry conjugates block scaling to L multiplication at set level. -/
theorem image_blockScaling_unitBall
    (lam : (rootNormedExtension T b)ˣ) :
    blockLinearIsometryEquiv T b ''
        (blockScalingContinuousAddEquiv (T := T) (b := b)
          (lam : rootNormedExtension T b) (Units.ne_zero lam) ''
            blockUnitBall T b) =
      (fun x => (lam : rootNormedExtension T b) * x) '' rootExtensionUnitBall T b := by
  rw [Set.image_image]
  have hfun : (blockLinearIsometryEquiv T b) ∘
      (blockScalingContinuousAddEquiv (T := T) (b := b)
        (lam : rootNormedExtension T b) (Units.ne_zero lam)) =
      fun x => (lam : rootNormedExtension T b) *
        (blockLinearIsometryEquiv T b) x := by
    funext x
    change (blockLinearIsometryEquiv T b)
      ((blockLinearIsometryEquiv T b).symm
        ((lam : rootNormedExtension T b) *
          (blockLinearIsometryEquiv T b) x)) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
  change ((blockLinearIsometryEquiv T b) ∘
    (blockScalingContinuousAddEquiv (T := T) (b := b)
      (lam : rootNormedExtension T b) (Units.ne_zero lam))) ''
      blockUnitBall T b =
    (fun x => (lam : rootNormedExtension T b) * x) ''
      rootExtensionUnitBall T b
  rw [hfun]
  rw [← Set.image_image]
  rw [blockLinearIsometryEquiv_image_blockUnitBall]

/-- Exact missing scalar factor equality after the set-level conjugacy. -/
structure BlockRootHaarFactorEqualityGap
    (lam : (rootNormedExtension T b)ˣ) where
  blockFactor : ENNReal
  blockFactor_eq : blockFactor =
    (thetaScalingHaarFactor (T := T) (b := b) (lam : rootNormedExtension T b)
      (Units.ne_zero lam) : ENNReal)
  rootFactor : ENNReal
  rootFactor_eq : rootFactor = rootHaarFactor T b lam
  equality : Prop

def BlockRootHaarFactorEqualityRequired
    (lam : (rootNormedExtension T b)ˣ) : Prop :=
  Nonempty (BlockRootHaarFactorEqualityGap (T := T) (b := b) lam)

end LeanFormal.IUT.XiFPaper.S278HaarFactorConjugacyActual

end
