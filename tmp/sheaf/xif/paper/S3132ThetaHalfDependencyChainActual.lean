import tmp.sheaf.xif.paper.S3132Task30ThetaHalfActual
import tmp.sheaf.xif.paper.S3134LastSeamExactMissingActual

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
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.S3132ThetaHalfDependencyChainActual

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
# task-38/task-41 dependency chain: the two raw Theta-half records are the same

**Component, not a paper object.**  Owner: hull.  Consumers: shehdd's
`S3134FourthTriangleResidual_of_exactMissing` and my task-30 residual.

shehdd's last-seam file records the raw Theta-half identification
`S3134LastSeamThetaHalf (I := I) D C3`
(`S3134Step3115ThetaPilotReadout = thetaPilotHullLogVolumeReal C3`), while
task-30 records it as the structure field
`MissingFourthTriangleThetaHalfReadout ... .theta_readout_eq`.  This module proves
the two records are **equivalent** (same actual equality, no convention change),
so either can be consumed by the other stream.  Recorded dependency order
(per shehdd's last-seam answer): the raw readout equality is
`-(D.detData.logVolume (S3134ThetaHullRegion D)).toReal =
Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal`
(`S3134LastSeamThetaHalf_iff_actual`), and it does NOT include the paper V-form
normalization.  The canonical rooted target `thetaPilotHullLogVolumeReal C3 =
S3131CanonicalRootedHC T mu` is obtained by composing this raw equality with the
task-41 normalization channel
(`S3132ThetaNormalizationFactorActual`), i.e.:
raw equality + normalization channel => canonical target; the carrier/fiber
comparison (`MissingC3PacketUniformComparison`) is needed only to push
`D.detData.logVolume` to the C3 packet.
-/

/-- **Equivalence of the two raw Theta-half records** (shehdd's last-seam half
and my task-30 minimal exact missing). -/
theorem S3134LastSeamThetaHalf_iff_missingThetaHalf
    (D : S1300HDDHullDetSource I) :
    S3134LastSeamThetaHalf (I := I) D C3 ↔
      MissingFourthTriangleThetaHalfReadout (I := I) (I0 := I0) C3 D := by
  constructor
  · intro h
    exact ⟨h⟩
  · intro h
    exact h.theta_readout_eq

/-- **Consumption form:** the task-30 minimal exact missing yields shehdd's raw
last-seam Theta half, and conversely. -/
theorem S3134LastSeamThetaHalf_of_missingThetaHalf
    (D : S1300HDDHullDetSource I)
    (M : MissingFourthTriangleThetaHalfReadout (I := I) (I0 := I0) C3 D) :
    S3134LastSeamThetaHalf (I := I) D C3 :=
  (S3134LastSeamThetaHalf_iff_missingThetaHalf (I := I) (I0 := I0) C3 D).mpr M

#check S3134LastSeamThetaHalf_iff_missingThetaHalf
#check S3134LastSeamThetaHalf_of_missingThetaHalf

end LeanFormal.IUT.XiFPaper.S3132ThetaHalfDependencyChainActual

end
