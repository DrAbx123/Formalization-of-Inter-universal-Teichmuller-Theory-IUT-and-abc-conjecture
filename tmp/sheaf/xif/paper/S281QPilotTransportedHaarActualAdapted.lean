import tmp.sheaf.xif.paper.S280QPilotBlockCLEActual
import tmp.sheaf.xif.paper.S247QPilotHaarInstancesActual
import tmp.sheaf.xif.paper.S232QPilotHaarTransportActual
import tmp.sheaf.xif.paper.S234QPilotHaarNormalizationActual
/-! # S281: product ContinuousAddEquiv and transported qPilot Haar/factor
Uses the per-b S280 ContinuousLinearEquiv to build the explicit product
ContinuousAddEquiv of the S191 carrier equivalence, gives the transported
qPilot product Haar instance, and instantiates the S234 factor. -/
noncomputable section
open scoped BigOperators
open scoped NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
namespace LeanFormal.IUT.XiFPaper.S281QPilotTransportedHaarActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.S172QPilotMultiradialImageActual
open LeanFormal.IUT.XiFPaper.S232QPilotHaarTransportActual
open LeanFormal.IUT.XiFPaper.S178QPilotObjectFullActual
open LeanFormal.IUT.XiFPaper.S191QPilotCarrierTransportActual
open LeanFormal.IUT.XiFPaper.S247QPilotHaarInstancesActual
open LeanFormal.IUT.XiFPaper.S280QPilotBlockCLEActual
open LeanFormal.IUT.XiFPaper.S234QPilotHaarNormalizationActual
open LeanFormal.IUT.XiFPaper.S22DependentProductActual
open LeanFormal.IUT.XiFPaper.S156QPilotSideObjectActual
open MeasureTheory
open MeasureTheory.Measure
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (Block (G := sourceQGeometry (l := l) T b))]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (Block (G := sourceQGeometry (l := l) T b))]
/-- Explicit product ContinuousAddEquiv of the S191 carrier equivalence. -/
noncomputable def s191ProductContinuousAddEquiv :
    DependentCompletionProduct T ≃ₜ+ QPilotMultiradialCarrier (l := l) T where
  toFun := s156ProductToBlock T
  invFun := fun y b => (s191BlockCLE T b).symm (y b)
  left_inv := by
    intro x; funext b; exact (s191BlockCLE T b).symm_apply_apply (x b)
  right_inv := by
    intro y; funext b; exact (s191BlockCLE T b).apply_symm_apply (y b)
  map_add' := by
    intro x y; funext b; exact (s191BlockCLE T b).map_add (x b) (y b)
  continuous_toFun := by
    change Continuous (fun x b => s191BlockCLE T b (x b))
    apply continuous_pi
    intro b
    exact (s191BlockCLE T b).continuous.comp (continuous_apply b)
  continuous_invFun := by
    change Continuous (fun y b => (s191BlockCLE T b).symm (y b))
    apply continuous_pi
    intro b
    exact (s191BlockCLE T b).symm.continuous.comp (continuous_apply b)
/-- Per-b dependent completion Haar instance. -/
instance dependentCompletionAddHaarIsAddHaar
    (b : Bad (nativePlaceSelection T)) :
    Measure.IsAddHaarMeasure
      (Measure.addHaar : Measure (DependentCompletion T b)) := by
  haveI : Nonempty (TopologicalSpace.PositiveCompacts (DependentCompletion T b)) := inferInstance
  rw [show (Measure.addHaar : Measure (DependentCompletion T b)) =
      Measure.addHaarMeasure (Classical.arbitrary
        (TopologicalSpace.PositiveCompacts (DependentCompletion T b))) from rfl]
  exact Measure.isAddHaarMeasure_addHaarMeasure _
/-- S156 qPilot ambient product Haar is additive Haar. -/
instance QPilotAmbientHaar_isAddHaar :
    Measure.IsAddHaarMeasure (QPilotAmbientHaar T) := by
  unfold QPilotAmbientHaar dependentCompletionHaar
  haveI : ∀ b : Bad (nativePlaceSelection T),
      SigmaFinite (Measure.addHaar : Measure (DependentCompletion T b)) := by
    intro b
    haveI : SecondCountableTopology (DependentCompletion T b) := inferInstance
    haveI : Nonempty (TopologicalSpace.PositiveCompacts (DependentCompletion T b)) := inferInstance
    rw [show (Measure.addHaar : Measure (DependentCompletion T b)) =
        Measure.addHaarMeasure (Classical.arbitrary
          (TopologicalSpace.PositiveCompacts (DependentCompletion T b))) from rfl]
    exact Measure.sigmaFinite_addHaarMeasure
  haveI : ∀ b : Bad (nativePlaceSelection T),
      MeasurableAdd (DependentCompletion T b) := fun b => inferInstance
  exact Measure.pi.isAddHaarMeasure (fun b => (Measure.addHaar :
    Measure (DependentCompletion T b)))
/-- Transported qPilot product Haar is additive Haar. -/
instance qPilotTransportedAmbientHaar_isAddHaar :
    Measure.IsAddHaarMeasure (qPilotTransportedAmbientHaar (l := l) T) := by
  have h := AddEquiv.isAddHaarMeasure_map
    (s191ProductContinuousAddEquiv T)
    (s191ProductContinuousAddEquiv T).continuous_toFun
    (s191ProductContinuousAddEquiv T).continuous_invFun
    (QPilotAmbientHaar T)
  simpa [qPilotTransportedAmbientHaar, s191ProductContinuousAddEquiv] using h
/-- Concrete S234 normalization factor. -/
noncomputable def qPilotHaarNormalizationFactorConcrete : ℝ≥0 :=
  (qPilotTransportedAmbientHaar (l := l) T).addHaarScalarFactor
    (QPilotMultiradialAmbientHaar (l := l) T (qPilotImageHaarFamily T))
/-- Concrete proportionality. -/
theorem qPilotTransported_eq_factor_smul_concrete
    [LocallyCompactSpace (QPilotMultiradialCarrier (l := l) T)]
    [SecondCountableTopology (QPilotMultiradialCarrier (l := l) T)] :
    qPilotTransportedAmbientHaar (l := l) T =
      (qPilotHaarNormalizationFactorConcrete T) •
        (QPilotMultiradialAmbientHaar (l := l) T (qPilotImageHaarFamily T)) :=
  isAddLeftInvariant_eq_smul
    (qPilotTransportedAmbientHaar (l := l) T)
    (QPilotMultiradialAmbientHaar (l := l) T (qPilotImageHaarFamily T))
end LeanFormal.IUT.XiFPaper.S281QPilotTransportedHaarActualAdapted
