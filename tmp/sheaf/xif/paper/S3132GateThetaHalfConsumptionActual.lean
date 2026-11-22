import tmp.sheaf.xif.paper.S3132ThetaHalfDependencyChainActual
import tmp.sheaf.xif.paper.S3134FourthJointQThetaActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3134Step3115To312Actual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3134LastSeamExactMissingActual
open LeanFormal.IUT.XiFPaper.S3132Task30ThetaHalfActual
open LeanFormal.IUT.XiFPaper.S3132ThetaHalfDependencyChainActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3132GateThetaHalfConsumptionActual

universe u v uv upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{0, uv, upi, umon, ui} l V)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
variable {V0 : Type} {I0 : OriginalInput l V0}
variable (C3 : SourcePilotRegionData (l := l) (V := V0) I0)
variable (P : PaperQPilotObjectActual (l := l) (I := I0))

/-!
# task-38/41 gate consumption: from shehdd's field-level Theta missing to task-30

**Component, not a paper object.**  Owner: hull.  Consumer: shehdd's gate /
`S3134FourthTriangleResidual_of_exactMissing` and the batch-A registry.

shehdd's field-level exact missing `S3134LastSeamThetaMissing (I := I) D C3` is
the raw equality

    -(D.detData.logVolume (S3134ThetaHullRegion D)).toReal
      = Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal,

while task-30's `MissingFourthTriangleThetaHalfReadout` is the readout equality
`S3134Step3115ThetaPilotReadout D = thetaPilotHullLogVolumeReal C3`.  This module
proves the consumption direction needed by the gate:
`S3134LastSeamThetaMissing → MissingFourthTriangleThetaHalfReadout`
(using shehdd's `S3134LastSeamThetaHalf_of_volume_eq` and the fact that the
last-seam Theta half is definitionally the task-30 field).  The reverse direction
would additionally require the V-form normalization channel (task-41), which is
NOT assumed here.
-/

/-- **Gate consumption:** shehdd's field-level Theta missing yields task-30's
minimal exact missing (raw readout convention). -/
theorem missingThetaHalf_of_lastSeamThetaMissing
    (D : S1300HDDHullDetSource I)
    (h : S3134LastSeamThetaMissing (I := I) D C3) :
    MissingFourthTriangleThetaHalfReadout (I := I) (I0 := I0) C3 D := by
  have h' : (D.detData.logVolume (S3134ThetaHullRegion (I := I) D)).toReal =
      -Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal :=
    neg_eq_iff_eq_neg.mp h
  have hhalf := S3134LastSeamThetaHalf_of_volume_eq (I := I) D C3 h'
  exact ⟨by
    simpa only [S3134LastSeamThetaHalf] using hhalf⟩

/-- **Consumption through the named equivalence** (task-30 record ↔ last-seam
half), for consumers that already have the last-seam half. -/
theorem missingThetaHalf_of_lastSeamThetaHalf
    (D : S1300HDDHullDetSource I)
    (h : S3134LastSeamThetaHalf (I := I) D C3) :
    MissingFourthTriangleThetaHalfReadout (I := I) (I0 := I0) C3 D :=
  (S3134LastSeamThetaHalf_iff_missingThetaHalf (I := I) (I0 := I0) C3 D).mp h

#check missingThetaHalf_of_lastSeamThetaMissing
#check missingThetaHalf_of_lastSeamThetaHalf

end LeanFormal.IUT.XiFPaper.S3132GateThetaHalfConsumptionActual

end