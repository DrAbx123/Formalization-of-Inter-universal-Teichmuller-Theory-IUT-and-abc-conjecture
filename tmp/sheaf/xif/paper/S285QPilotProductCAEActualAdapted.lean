import tmp.sheaf.xif.paper.S280QPilotBlockCLEActual
/-! # S285: explicit product ContinuousAddEquiv from per-b CLE
Only the product additive equivalence is built here, using per-b s191BlockCLE.
No Haar/transported statements yet. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
namespace LeanFormal.IUT.XiFPaper.S285QPilotProductCAEActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.S191QPilotCarrierTransportActual
open LeanFormal.IUT.XiFPaper.S172QPilotMultiradialImageActual
open LeanFormal.IUT.XiFPaper.S280QPilotBlockCLEActual
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
example (b : Bad (nativePlaceSelection T)) :
    s191TensorFamily T b () = DependentCompletion T b := rfl
/-- Explicit product ContinuousAddEquiv of the carrier equivalence. -/
noncomputable def s191ProductContinuousAddEquiv :
    DependentCompletionProduct T ≃ₜ+ QPilotMultiradialCarrier (l := l) T where
  toFun := s156ProductToBlock T
  invFun := fun y b =>
    (s191BlockCLE T b (y b) : DependentCompletion T b)
  left_inv := by
    intro x; funext b; exact (s191BlockCLE T b).apply_symm_apply (x b)
  right_inv := by
    intro y; funext b; exact (s191BlockCLE T b).symm_apply_apply (y b)
  map_add' := by
    intro x y; funext b; exact (s191BlockCLE T b).symm.map_add (x b) (y b)
  continuous_toFun := by
    change Continuous (fun (x : DependentCompletionProduct T)
      (b : Bad (nativePlaceSelection T)) => (s191BlockCLE T b).symm (x b))
    apply continuous_pi
    intro b
    exact (s191BlockCLE T b).symm.continuous.comp
      (continuous_apply b : Continuous (fun x : DependentCompletionProduct T =>
        (x b : s191TensorFamily T b ())))
  continuous_invFun := by
    change Continuous (fun (y : QPilotMultiradialCarrier (l := l) T)
      (b : Bad (nativePlaceSelection T)) =>
        (s191BlockCLE T b (y b) : DependentCompletion T b))
    apply continuous_pi
    intro b
    exact (s191BlockCLE T b).continuous.comp
      (continuous_apply b : Continuous (fun y : QPilotMultiradialCarrier (l := l) T =>
        (y b : QPilotMultiradialFiber (l := l) T b)))
end LeanFormal.IUT.XiFPaper.S285QPilotProductCAEActualAdapted
