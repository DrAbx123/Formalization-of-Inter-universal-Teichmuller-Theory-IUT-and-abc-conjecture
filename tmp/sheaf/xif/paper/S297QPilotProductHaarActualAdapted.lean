import tmp.sheaf.xif.paper.S280QPilotBlockCLEActual
/-! # S297: cast the S280 target to DependentCompletion and build product CAE
The per-b CLE target is cast along the definitional type equality
s191TensorFamily T b () = DependentCompletion T b.  The product additive
equivalence then has unified fiber types, so continuous_apply no longer infers a
wrong codomain. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
namespace LeanFormal.IUT.XiFPaper.S297QPilotProductHaarActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.S172QPilotMultiradialImageActual
open LeanFormal.IUT.XiFPaper.S191QPilotCarrierTransportActual
open LeanFormal.IUT.XiFPaper.S280QPilotBlockCLEActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S22DependentProductActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (Block (G := sourceQGeometry (l := l) T b))]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (Block (G := sourceQGeometry (l := l) T b))]
/-- Module structure of the dependent completion over its Qp. -/
instance dependentCompletionModuleQp (b : Bad (nativePlaceSelection T)) :
    Module ℚ_[qVFamTensorP T b] (DependentCompletion T b) :=
  inferInstanceAs (Module ℚ_[qVFamTensorP T b] (s191TensorFamily T b ()))

/-- Definitional type equality of the two carrier fibers. -/
theorem s191FiberType_eq (b : Bad (nativePlaceSelection T)) :
    s191TensorFamily T b () = DependentCompletion T b := rfl
/-- Cast identity CLE from the tensor family to the dependent completion. -/
noncomputable def s191DepCastCLE (b : Bad (nativePlaceSelection T)) :
    s191TensorFamily T b () ≃L[ℚ_[qVFamTensorP T b]] DependentCompletion T b :=
  ContinuousLinearEquiv.refl ℚ_[qVFamTensorP T b] (s191TensorFamily T b ())
/-- Per-b CLE with target changed to DependentCompletion. -/
noncomputable def s191BlockCLEToDep (b : Bad (nativePlaceSelection T)) :
    Block (G := sourceQGeometry (l := l) T b) ≃L[ℚ_[qVFamTensorP T b]]
      DependentCompletion T b :=
  (s191BlockCLE T b).trans (s191DepCastCLE T b)
/-- Product ContinuousAddEquiv with unified fiber types. -/
noncomputable def s191ProductContinuousAddEquiv :
    DependentCompletionProduct T ≃ₜ+ QPilotMultiradialCarrier (l := l) T where
  toFun := fun x b => (s191BlockCLEToDep T b).symm (x b)
  invFun := fun y b => s191BlockCLEToDep T b (y b)
  left_inv := by
    intro x; funext b; exact (s191BlockCLEToDep T b).apply_symm_apply (x b)
  right_inv := by
    intro y; funext b; exact (s191BlockCLEToDep T b).symm_apply_apply (y b)
  map_add' := by
    intro x y; funext b;
    exact (s191BlockCLEToDep T b).symm.map_add (x b) (y b)
  continuous_toFun := by
    change Continuous (fun (x : DependentCompletionProduct T)
      (b : Bad (nativePlaceSelection T)) =>
        (s191BlockCLEToDep T b).symm (x b))
    apply continuous_pi
    intro b
    exact (s191BlockCLEToDep T b).symm.continuous.comp
      (continuous_apply b : Continuous (fun x : DependentCompletionProduct T => x b))
  continuous_invFun := by
    change Continuous (fun (y : QPilotMultiradialCarrier (l := l) T)
      (b : Bad (nativePlaceSelection T)) =>
        s191BlockCLEToDep T b (y b))
    apply continuous_pi
    intro b
    exact (s191BlockCLEToDep T b).continuous.comp
      (continuous_apply b : Continuous (fun y : QPilotMultiradialCarrier (l := l) T => y b))
end LeanFormal.IUT.XiFPaper.S297QPilotProductHaarActualAdapted
