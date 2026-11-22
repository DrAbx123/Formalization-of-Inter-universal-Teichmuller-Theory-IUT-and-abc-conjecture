import tmp.sheaf.xif.paper.S280QPilotBlockCLEActual
import tmp.sheaf.xif.paper.S232QPilotHaarTransportActual
import tmp.sheaf.xif.paper.S247QPilotHaarInstancesActual
import Mathlib.MeasureTheory.Constructions.Pi
/-! # S304: transported qPilot Haar via per-b pushforward and product
Bypasses product CLE.  The transported ambient measure is the product of the
per-b pushforwards of addHaar along s191BlockCLE.symm (= s156FiberToBlock).
Each pushforward is Haar by ContinuousLinearEquiv.isAddHaarMeasure_map; the
product is Haar by Measure.pi.isAddHaarMeasure. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
namespace LeanFormal.IUT.XiFPaper.S304QPilotTransportedHaarActual
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
open LeanFormal.IUT.XiFPaper.S22DependentProductActual
open LeanFormal.IUT.XiFPaper.S156QPilotSideObjectActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
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
/-- Per-b DependentCompletion Haar instance. -/
instance dependentCompletionAddHaarIsAddHaar
    (b : Bad (nativePlaceSelection T)) :
    Measure.IsAddHaarMeasure
      (Measure.addHaar : Measure (DependentCompletion T b)) := by
  haveI : Nonempty (TopologicalSpace.PositiveCompacts (DependentCompletion T b)) := inferInstance
  rw [show (Measure.addHaar : Measure (DependentCompletion T b)) =
      Measure.addHaarMeasure (Classical.arbitrary
        (TopologicalSpace.PositiveCompacts (DependentCompletion T b))) from rfl]
  exact Measure.isAddHaarMeasure_addHaarMeasure _
/-- Continuity of the per-b carrier embedding. -/
theorem continuous_s156FiberToBlock (b : Bad (nativePlaceSelection T)) :
    Continuous (s156FiberToBlock T b) := by
  change Continuous ((s191BlockCLE T b).symm)
  exact (s191BlockCLE T b).symm.continuous

/-- Per-b pushforward Haar on Block. -/
instance blockPushforwardAddHaarIsAddHaar
    (b : Bad (nativePlaceSelection T)) :
    Measure.IsAddHaarMeasure
      ((Measure.addHaar : Measure (DependentCompletion T b)).map
        (s156FiberToBlock T b)) := by
  haveI : MeasurableSpace (s191TensorFamily T b ()) :=
    inferInstanceAs (MeasurableSpace (DependentCompletion T b))
  haveI : Measure.IsAddHaarMeasure
      (Measure.addHaar : Measure (s191TensorFamily T b ())) :=
    inferInstanceAs (Measure.IsAddHaarMeasure
      (Measure.addHaar : Measure (DependentCompletion T b)))
  have h := ContinuousLinearEquiv.isAddHaarMeasure_map
    (s191BlockCLE T b).symm
    (Measure.addHaar : Measure (s191TensorFamily T b ()))
  simpa [s156FiberToBlock, s191BlockCLE] using h
/-- The transported ambient measure is the product of per-b pushforwards. -/
theorem qPilotTransportedAmbientHaar_eq_pi_map :
    qPilotTransportedAmbientHaar (l := l) T =
      Measure.pi (fun b : Bad (nativePlaceSelection T) =>
        (Measure.addHaar : Measure (DependentCompletion T b)).map
          (s156FiberToBlock T b)) := by
  rw [qPilotTransportedAmbientHaar, QPilotAmbientHaar, dependentCompletionHaar]
  change Measure.map (fun x b => s156FiberToBlock T b (x b))
      (Measure.pi (fun b => (Measure.addHaar : Measure (DependentCompletion T b)))) =
    Measure.pi (fun b => (Measure.addHaar : Measure (DependentCompletion T b)).map
      (s156FiberToBlock T b))
  haveI : ∀ b : Bad (nativePlaceSelection T),
      SigmaFinite ((Measure.addHaar : Measure (DependentCompletion T b)).map
        (s156FiberToBlock T b)) := fun b => inferInstance
  apply Measure.pi_map_pi
  intro b
  exact (continuous_s156FiberToBlock T b).aemeasurable
/-- The transported ambient measure is additive Haar. -/
instance qPilotTransportedAmbientHaar_isAddHaar :
    Measure.IsAddHaarMeasure (qPilotTransportedAmbientHaar (l := l) T) := by
  rw [qPilotTransportedAmbientHaar_eq_pi_map T]
  haveI : ∀ b : Bad (nativePlaceSelection T),
      SigmaFinite ((Measure.addHaar : Measure (DependentCompletion T b)).map
        (s156FiberToBlock T b)) := fun b => inferInstance
  haveI : ∀ b : Bad (nativePlaceSelection T),
      MeasurableAdd (Block (G := sourceQGeometry (l := l) T b)) := fun b => inferInstance
  exact Measure.pi.isAddHaarMeasure (fun b =>
    (Measure.addHaar : Measure (DependentCompletion T b)).map (s156FiberToBlock T b))
end LeanFormal.IUT.XiFPaper.S304QPilotTransportedHaarActual
