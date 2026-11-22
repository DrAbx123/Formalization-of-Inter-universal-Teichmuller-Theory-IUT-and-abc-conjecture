import tmp.sheaf.xif.paper.S369OtriSplitFrobenioidActual
import tmp.sheaf.xif.paper.S373NativeStageSplittingActual
import tmp.sheaf.xif.paper.S376StageTauConstructionActual
/-! # S379: native-stage tau submonoid, or weakest exact missing theorem
The actual native stage presentation and rationalMonoidTransport are S369.
An actual tau-family is a submonoid of O^triangle(X) for each isotropic X,
with the five Definition 2.3 laws.  No such family is constructed in the repo:
the weakest exact missing theorem is Nonempty (CharacteristicSplitting stageTransport),
equivalent to Nonempty tau-data.  This file records that equivalence only; it
does not fake a split. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
namespace LeanFormal.IUT.XiFPaper.S379NativeStageTauExactMissingActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S369OtriSplitFrobenioidActual
open LeanFormal.IUT.XiFPaper.S373NativeStageSplittingActual
open LeanFormal.IUT.XiFPaper.S376StageTauConstructionActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- Actual stage presentation. -/
abbrev StagePresentation : Iut.FrobenioidPresentation :=
  nativeStageFrobenioidPresentation T b
/-- Actual stage rational monoid transport. -/
abbrev StageTransport :
    (StagePresentation T b).preFrobenioid.RationalMonoidTransport :=
  nativeStageRationalMonoidTransport T b
/-- Exact tau-family object: submonoids of O^triangle with the five laws. -/
abbrev NativeStageTauData : Type :=
  StageCharacteristicTauData (T := T) (b := b)
/-- Weakest exact missing theorem: an actual tau-family. -/
def NativeStageTauSubmonoidRequired : Prop :=
  Nonempty (NativeStageTauData T b)
/-- Weakest exact missing theorem: a characteristic splitting. -/
def NativeStageCharacteristicSplittingRequired : Prop :=
  Nonempty ((StagePresentation T b).preFrobenioid.CharacteristicSplitting
    (StageTransport T b))
/-- Supplying tau data is exactly supplying a CharacteristicSplitting. -/
theorem nativeStageTauSubmonoidRequired_iff :
    NativeStageTauSubmonoidRequired T b ↔
      NativeStageCharacteristicSplittingRequired T b := by
  simpa only [NativeStageTauSubmonoidRequired, NativeStageTauData,
    NativeStageCharacteristicSplittingRequired, StagePresentation, StageTransport,
    NativeStageCharacteristicSplittingMissing,
    NativeStageCharacteristicSplittingExact] using
    (nativeStageCharacteristicSplittingMissing_iff T b).symm
/-- Exact missing theorem recognized by the repo. -/
theorem nativeStageCharacteristicSplitting_missing :
    NativeStageCharacteristicSplittingMissing T b ↔
      NativeStageTauSubmonoidRequired T b := by
  simpa only [NativeStageTauSubmonoidRequired, NativeStageTauData,
    NativeStageCharacteristicSplittingExact] using
    nativeStageCharacteristicSplittingMissing_iff T b
end LeanFormal.IUT.XiFPaper.S379NativeStageTauExactMissingActual
