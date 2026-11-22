import tmp.sheaf.xif.paper.S2040RootStackThetaPilotActual
import tmp.sheaf.xif.paper.S2038PaperOActual
import tmp.sheaf.xif.paper.S1978LocalFieldOCarrierActual
import tmp.sheaf.xif.paper.S2032R6GeneratorActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.LGPThetaActionActual
open LeanFormal.IUT.XiFPaper.S2040RootStackThetaPilotActual
open LeanFormal.IUT.XiFPaper.S2038PaperOActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S2032R6GeneratorActual
namespace LeanFormal.IUT.XiFPaper.S2053PaperORootStackAlignment
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- Component (d) alignment: the actual root-stack Theta-pilot object. -/
abbrev S2053ComponentD (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :=
  S2040RootStackThetaPilotObject (l := l) T b
theorem S2053ComponentD_available :
    Nonempty (S2053ComponentD (l := l) T b) :=
  s2040RootStackThetaPilotObject_available (l := l) T b
theorem S2053ComponentD_root_pow :
    (s2040RootStackThetaPilotObject (l := l) T b).root ^ (2 * l.value) =
      qVAlgClosedUnit T b :=
  s2040Root_pow (l := l) T b
theorem S2053ComponentD_theta_value (j : LGPThetaIndex l) :
    (s2040RootStackThetaPilotObject (l := l) T b).thetaAction.value j =
      lgpThetaValue (l := l) T b j :=
  s2040Root_theta_value (l := l) T b j
/-- Exact missing paper O^×/O^×μ/ambient carrier attached to (d). -/
abbrev S2053PaperOUnitsMuAmbientRequired : Type 1 := S2040PaperOUnitsMuAmbient
/-- Exact missing completion-level/rebased paper input. -/
abbrev S2053RebasedPaperInputRequired
    (D : S1895OIdentificationsActual.S1895PaperInput) : Type 1 :=
  S1978RebasedPaperInput D
/-- Exact missing completion-level O^×/O^◃ carrier identification. -/
def S2053CompletionCarrierIdentificationRequired : Prop :=
  Nonempty (S2040PaperOUnitsMuAmbient)
#check S2053ComponentD_available
#check S2053ComponentD_root_pow
#check S2053ComponentD_theta_value
#check S2053PaperOUnitsMuAmbientRequired
#check S2053RebasedPaperInputRequired
#check S2053CompletionCarrierIdentificationRequired
end LeanFormal.IUT.XiFPaper.S2053PaperORootStackAlignment
end
