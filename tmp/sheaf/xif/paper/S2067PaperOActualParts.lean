import tmp.sheaf.xif.paper.S2038PaperOActual
import tmp.sheaf.xif.paper.S2040S2060Actual
import tmp.sheaf.xif.paper.S2040S2057InterfaceActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S2040S2060Actual
open LeanFormal.IUT.XiFPaper.S2040S2057InterfaceActual
open LeanFormal.IUT.XiFPaper.S2040PaperOUnitsMuAmbientActual
open LeanFormal.IUT.XiFPaper.S2040RootStackThetaPilotActual
open LeanFormal.IUT.XiFPaper.S2057RootStackThetaPilotActual
open LeanFormal.IUT.XiFPaper.S2046CompletionOUnitsActual
namespace LeanFormal.IUT.XiFPaper.S2067PaperOActualParts
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- Actual components available for PaperO: corrected O^/O^mu/ambient,
the S2057 finite root-stack Theta-pilot, and the unconditional norm bridge.
These are the S2040S2060/S2040S2057 actual pieces. -/
structure S2067PaperOActualParts where
  oUnitsMuAmbient : S2040PaperOUnitsMuAmbient
  thetaPilot : S2057RootStackThetaPilotObject (l := l) T b
  normBridge : ∀ v : FinitePrimePlace 2 7, S2046NormBridge v
noncomputable def s2067PaperOActualParts :
    S2067PaperOActualParts T b where
  oUnitsMuAmbient := s2040PaperOUnitsMuAmbientActual T b
  thetaPilot := s2040S2057ThetaPilotObject T b
  normBridge := fun v => s2040NormBridgeUnconditional v
theorem s2067PaperOActualParts_nonempty :
    Nonempty (S2067PaperOActualParts T b) :=
  ⟨s2067PaperOActualParts T b⟩
/-- Exact missing paper O^tri/q_v/O^×mu attachment (S2040S2057Interface). -/
abbrev S2067PaperOtriMissing : Type 1 :=
  S2040PaperOtriAttachmentRequired (l := l) T b
#check s2067PaperOActualParts
#check s2067PaperOActualParts_nonempty
#check S2067PaperOtriMissing
end LeanFormal.IUT.XiFPaper.S2067PaperOActualParts
end
