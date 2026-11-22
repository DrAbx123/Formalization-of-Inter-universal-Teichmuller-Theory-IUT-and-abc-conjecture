import tmp.sheaf.xif.paper.Mzk1StepXICleanHqnegGateActual
import tmp.sheaf.xif.paper.Mzk1StepXIDischargedGateV2Actual
import tmp.sheaf.xif.paper.Mzk1StepXIHqnegDispatchedAcceptanceActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi gate verification

Re-exports the three green hqneg gates and records their axiom gates. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIGateVerificationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXICleanHqnegGateActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIHqnegCoercionActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIHqnegDispatchedAcceptanceActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_gate_verification (R : PaperKummerReading T)
    (h : R.qReading < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T R
        (stepxi_hqneg_of_qReading_neg T R h) ipl hipl she hshe apt hapt) :=
  stepxi_clean_hqneg_gate T R h ipl hipl she hshe apt hapt

#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXICleanHqnegGateActual.stepxi_clean_hqneg_gate
#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIHqnegDispatchedAcceptanceActual.stepxi_hqneg_dispatched_acceptance

end LeanFormal.IUT.XiFPaper.Mzk1StepXIGateVerificationActual

end
