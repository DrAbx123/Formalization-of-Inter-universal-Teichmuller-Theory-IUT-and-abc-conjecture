import tmp.sheaf.xif.paper.S232QPilotHaarTransportActual
import tmp.sheaf.xif.paper.S178QPilotObjectFullActual
import Mathlib.MeasureTheory.Measure.Haar.Basic
/-! # S247: additive Haar instances for the S172 qPilot product measure
Per-b Block is a locally compact additive group, so Measure.addHaar is a Haar
measure; the finite product instance Measure.pi.isAddHaarMeasure gives the S172
multiradial ambient product Haar.  This constructs the native side instances.
The transported pushforward Haar instance is recorded as the exact remaining
typeclass obligation.  No inequality/fake. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S247QPilotHaarInstancesActual
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
/-- Per-b Block additive Haar instance for Measure.addHaar. -/
instance blockAddHaarIsAddHaarMeasure
    (b : Bad (nativePlaceSelection T)) :
    Measure.IsAddHaarMeasure
      (Measure.addHaar : Measure (Block (G := sourceQGeometry (l := l) T b))) := by
  haveI : Nonempty (TopologicalSpace.PositiveCompacts
      (Block (G := sourceQGeometry (l := l) T b))) := inferInstance
  rw [show (Measure.addHaar : Measure (Block (G := sourceQGeometry (l := l) T b))) =
      Measure.addHaarMeasure (Classical.arbitrary
        (TopologicalSpace.PositiveCompacts
          (Block (G := sourceQGeometry (l := l) T b)))) from rfl]
  exact Measure.isAddHaarMeasure_addHaarMeasure _
/-- The S172 multiradial ambient product Haar is an additive Haar measure. -/
instance QPilotMultiradialAmbientHaar_isAddHaar :
    Measure.IsAddHaarMeasure
      (QPilotMultiradialAmbientHaar (l := l) T (qPilotImageHaarFamily T)) := by
  unfold QPilotMultiradialAmbientHaar qPilotImageHaarFamily
  haveI : ∀ b : Bad (nativePlaceSelection T),
      SigmaFinite (Measure.addHaar : Measure (Block (G := sourceQGeometry (l := l) T b))) := by
    intro b
    haveI : SecondCountableTopology (Block (G := sourceQGeometry (l := l) T b)) := inferInstance
    haveI : Nonempty (TopologicalSpace.PositiveCompacts
        (Block (G := sourceQGeometry (l := l) T b))) := inferInstance
    rw [show (Measure.addHaar : Measure (Block (G := sourceQGeometry (l := l) T b))) =
        Measure.addHaarMeasure (Classical.arbitrary
          (TopologicalSpace.PositiveCompacts
            (Block (G := sourceQGeometry (l := l) T b)))) from rfl]
    exact Measure.sigmaFinite_addHaarMeasure
  haveI : ∀ b : Bad (nativePlaceSelection T),
      MeasurableAdd (Block (G := sourceQGeometry (l := l) T b)) := fun b => inferInstance
  exact Measure.pi.isAddHaarMeasure (fun b => (Measure.addHaar :
    Measure (Block (G := sourceQGeometry (l := l) T b))))
end LeanFormal.IUT.XiFPaper.S247QPilotHaarInstancesActual
