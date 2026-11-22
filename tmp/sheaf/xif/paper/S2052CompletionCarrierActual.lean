import tmp.sheaf.xif.paper.S2038PaperOActual
import tmp.sheaf.xif.paper.S2032R6GeneratorActual
import tmp.sheaf.xif.paper.S1978LocalFieldOCarrierActual
import tmp.sheaf.xif.paper.S2045OperationKummerActual
import tmp.sheaf.xif.paper.S2046OperationComponentsActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual
open LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual
open LeanFormal.IUT.XiFPaper.S1968QVDeterminedQPilotActual
open LeanFormal.IUT.XiFPaper.S1979QPilotStripFromDivisorActual
open LeanFormal.IUT.XiFPaper.S2032R6GeneratorActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S2045OperationKummerActual
open LeanFormal.IUT.XiFPaper.S2046OperationComponentsActual
namespace LeanFormal.IUT.XiFPaper.S2052CompletionCarrierActual
local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
/-- The exact completion-level carrier/rebasing datum still missing. -/
abbrev S2052CompletionCarrierRequired (D : S1895PaperInput) : Type 1 :=
  S1978RebasedPaperInput D
/-- Actual Q_p-model q_v elements are available at every bad place. -/
noncomputable def S2052QpModelQ (D : S1895PaperInput)
    (b : (S1951KummerEvaluationSquareActual.paperInput D).initial.badPlaces) : LocalOFieldIntegral 5 :=
  localOFieldQParameter D b
theorem S2052QpModelQ_norm (D : S1895PaperInput)
    (b : (S1951KummerEvaluationSquareActual.paperInput D).initial.badPlaces) :
    ‖(S2052QpModelQ D b : AlgebraicClosure ℚ_[5])‖ = paperQV D b :=
  localOFieldQParameter_norm D b
#check S2052CompletionCarrierRequired
#check S2052QpModelQ_norm
#check S2045OperationKummerData
#check S2045OperationKummerRequired
#check S2046OperationComponentsRequired
end LeanFormal.IUT.XiFPaper.S2052CompletionCarrierActual
end
