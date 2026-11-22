import tmp.sheaf.xif.paper.S373NativeStageSplittingActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S376StageTauConstructionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S369OtriSplitFrobenioidActual
open LeanFormal.IUT.XiFPaper.S373NativeStageSplittingActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- From a supplied CharacteristicSplitting of the actual stage transport,
construct StageCharacteristicTauData directly from its fields. -/
noncomputable def stageTauDataOfSplitting
    (C : (nativeStageFrobenioidPresentation T b).preFrobenioid.CharacteristicSplitting
      (nativeStageRationalMonoidTransport T b)) :
    StageCharacteristicTauData (T := T) (b := b) where
  tau := fun X => C.tau X
  pullback_mem := C.pullback_mem
  units_commute := C.units_commute
  multiplication_bijective := C.multiplication_bijective
  isotropicHull_mem_range := C.isotropicHull_mem_range

/-- The exact missing datum: a CharacteristicSplitting of the actual stage
transport.  This is the weakest statement from which tau X can be defined. -/
def NativeStageCharacteristicSplittingMissing
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty ((nativeStageFrobenioidPresentation T b).preFrobenioid.CharacteristicSplitting
    (nativeStageRationalMonoidTransport T b))

/-- Supplying the missing splitting is equivalent to supplying tau data. -/
theorem nativeStageCharacteristicSplittingMissing_iff :
    NativeStageCharacteristicSplittingMissing T b ↔
      NativeStageCharacteristicSplittingExact (T := T) (b := b) := by
  unfold NativeStageCharacteristicSplittingMissing
    NativeStageCharacteristicSplittingExact
  exact (nativeStageCharacteristicSplittingExact_iff T b).symm

end LeanFormal.IUT.XiFPaper.S376StageTauConstructionActual

end
