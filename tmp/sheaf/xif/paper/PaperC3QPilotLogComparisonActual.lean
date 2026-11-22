import tmp.sheaf.xif.paper.PaperC3SourceQHullRelationActual
import tmp.sheaf.xif.paper.PaperC3SourceDataQConsistencyActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import Mathlib.MeasureTheory.Measure.Haar.Basic

-- S164: actual Haar/log volumes on the one-factor qUnit block and the
-- paper/source hull comparison.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperC3QPilotLogComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceDataQConsistencyActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.GenericQPilotCompletionPowerActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

-- Actual additive Haar measures on the one-factor blocks.
instance paperQUnitBlockMeasurableSpace :
    MeasurableSpace (Block (G := sourceQGeometry (l := l) T b)) := borel _

instance sourceQTensorMeasurableSpace :
    MeasurableSpace (SourceQTensorBlock T b) := borel _

noncomputable instance paperQUnitBlockBorelSpace :
    BorelSpace (Block (G := sourceQGeometry (l := l) T b)) := ⟨rfl⟩

noncomputable instance sourceQTensorBorelSpace :
    BorelSpace (SourceQTensorBlock T b) := ⟨rfl⟩

noncomputable def paperQUnitBlockHaar :
    Measure (Block (G := sourceQGeometry (l := l) T b)) :=
  Measure.addHaar

noncomputable def sourceQTensorHaar :
    Measure (SourceQTensorBlock T b) :=
  Measure.addHaar

-- Actual Haar log-volumes.
noncomputable def paperQUnitBlockLogVolume
    (S : Set (Block (G := sourceQGeometry (l := l) T b))) : ENNReal :=
  haarLogVolume (paperQUnitBlockHaar T b) S

noncomputable def sourceQTensorLogVolume
    (S : Set (SourceQTensorBlock T b)) : ENNReal :=
  haarLogVolume (sourceQTensorHaar T b) S

-- Actual paper qUnit hull log <= source qUnit hull log, from the S143 inclusion
-- and actual Haar-log monotonicity.
theorem paperQUnitHull_logVolume_le_sourceQHull_logVolume :
    paperQUnitBlockLogVolume T b
      (paperQUnitLambdaHull (G := sourceQGeometry (l := l) T b)) ≤
      sourceQTensorLogVolume T b
        (sourceQTensorLambdaOHull T b) := by
  let h := qParameterUnitLambdaHull_subset_sourceQHullInPaperBlock T b
  have hlog := haarLogVolume_mono (μ := paperQUnitBlockHaar T b) h
  unfold paperQUnitBlockLogVolume paperQUnitBlockHaar at hlog
  unfold sourceQTensorLogVolume sourceQTensorHaar
  exact hlog

-- Exact qPilot-region log comparison gap: the region inclusion/log inequality
-- is not asserted; only the paper qUnit hull bound above is actual.
structure GenericQPilotLogComparisonGap
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  qPilotRegionLogVolume : ENNReal
  sourceQHullLogVolume : ENNReal
  comparison : Prop
  comparison_eq : comparison = (qPilotRegionLogVolume ≤ sourceQHullLogVolume)

noncomputable def genericQPilotLogComparisonGap :
    GenericQPilotLogComparisonGap T b where
  qPilotRegionLogVolume :=
    paperQUnitBlockLogVolume T b
      (genericQPilotRegion (G := sourceQGeometry (l := l) T b))
  sourceQHullLogVolume := sourceQTensorLogVolume T b (sourceQTensorLambdaOHull T b)
  comparison := (paperQUnitBlockLogVolume T b
      (genericQPilotRegion (G := sourceQGeometry (l := l) T b)) ≤
        sourceQTensorLogVolume T b (sourceQTensorLambdaOHull T b))
  comparison_eq := rfl

#check paperQUnitBlockHaar
#check sourceQTensorHaar
#check paperQUnitBlockLogVolume
#check sourceQTensorLogVolume
#check paperQUnitHull_logVolume_le_sourceQHull_logVolume
#check GenericQPilotLogComparisonGap
#check genericQPilotLogComparisonGap

end LeanFormal.IUT.XiFPaper.PaperC3QPilotLogComparisonActual

end