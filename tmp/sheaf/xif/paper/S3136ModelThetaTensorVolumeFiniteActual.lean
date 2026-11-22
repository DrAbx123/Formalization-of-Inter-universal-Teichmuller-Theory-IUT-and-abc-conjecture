import tmp.sheaf.xif.paper.S3136NativeHaarFamilyActual

/-! # Stage-4 host: finiteness of native Haar volumes on compact tensor regions

Source anchors: IUT III, Prop. 3.2, (ii) (compact tensor log-shell regions with
additive Haar); IUT III, Remark 3.9.4 (log-volumes); IUT II, Remark 2.5.1, (i).

This is the first constructible piece of the IUT IV Section 2-style estimate
field (c) `regionVolume_le_normalizedWeight`: the additive-Haar volume of any
COMPACT tensor region is finite (IsAddHaarMeasure extends
IsFiniteMeasureOnCompacts).  The comparison against the normalized weight is a
separate analytic estimate and is NOT claimed here.

LABEL: prerequisite component.  Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ModelThetaTensorVolumeFiniteActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open MeasureTheory

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The native additive Haar family satisfies finite-measure-on-compacts (parent
instance of the additive Haar property). -/
instance lgpNativeHaarFamily_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts (lgpNativeHaarFamily T b) := by
  haveI : Measure.IsAddHaarMeasure (lgpNativeHaarFamily T b) :=
    lgpNativeHaarFamily_isAddHaar T b
  infer_instance

/-- The native Haar volume of a compact tensor region is finite. -/
theorem lgpNativeHaarFamily_measure_lt_top_of_isCompact
    {S : Set (qVFamTensorBlock T b)} (hS : IsCompact S) :
    lgpNativeHaarFamily T b S < ⊤ :=
  IsCompact.measure_lt_top hS

#check lgpNativeHaarFamily_isFiniteMeasureOnCompacts
#check lgpNativeHaarFamily_measure_lt_top_of_isCompact

end LeanFormal.IUT.XiFPaper.S3136ModelThetaTensorVolumeFiniteActual
end