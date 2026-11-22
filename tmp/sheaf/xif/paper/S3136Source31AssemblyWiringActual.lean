import tmp.sheaf.xif.paper.S3136Source31RemainingSlotsActual
import tmp.sheaf.xif.paper.S3136Source31SlotWiringActual

/-! # Stage-4 host: complete SourceDefinition31Data assembly wiring theorems

Source anchor: IUT I, Definition 3.1.

CONSUMER: qpilot's modelSourceDefinition31Data assembly. Field-level wiring
theorems for `lgpSource31Data_full`: the reduction slot is exactly the native
reduction clause provider, the selected/bad place types and arithmetic are the
native ones, and the remaining slots/pairs are the passed data. This lets the
assembly be checked field by field.

LABEL: wiring component. Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136Source31AssemblyWiringActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.NativeSplitSufficientConditionActual
open LeanFormal.IUT.XiFPaper.S3136Source31RemainingSlotsActual
open LeanFormal.IUT.XiFPaper.S3136ModelReductionClauseProviderActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The reduction slot of the complete assembly is the native reduction clause provider. -/
theorem lgpSource31Data_full_reduction
    (F : NativeSplitInputFamily (l := l) T)
    (R : LGPModelRemainingSlots l)
    (C : LGPModelCompatPairs) :
    (lgpSource31Data_full (l := l) T F R C).reduction =
      lgpModelReductionClauseProvider (l := l) T F := rfl

/-- The selected places of the complete assembly are the native selected places. -/
theorem lgpSource31Data_full_selectedPlaces
    (F : NativeSplitInputFamily (l := l) T)
    (R : LGPModelRemainingSlots l)
    (C : LGPModelCompatPairs) :
    (lgpSource31Data_full (l := l) T F R C).selectedPlaces =
      Selected (nativePlaceSelection T) := rfl

/-- The bad places of the complete assembly are the native bad places. -/
theorem lgpSource31Data_full_badPlaces
    (F : NativeSplitInputFamily (l := l) T)
    (R : LGPModelRemainingSlots l)
    (C : LGPModelCompatPairs) :
    (lgpSource31Data_full (l := l) T F R C).badPlaces =
      Bad (nativePlaceSelection T) := rfl

/-- The torsion slot of the complete assembly is the passed torsion clause. -/
theorem lgpSource31Data_full_torsion
    (F : NativeSplitInputFamily (l := l) T)
    (R : LGPModelRemainingSlots l)
    (C : LGPModelCompatPairs) :
    (lgpSource31Data_full (l := l) T F R C).torsion = R.torsion := rfl

#check lgpSource31Data_full_reduction
#check lgpSource31Data_full_selectedPlaces
#check lgpSource31Data_full_badPlaces
#check lgpSource31Data_full_torsion

end LeanFormal.IUT.XiFPaper.S3136Source31AssemblyWiringActual
end