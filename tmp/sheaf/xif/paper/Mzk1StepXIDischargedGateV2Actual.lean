import tmp.sheaf.xif.paper.Mzk1StepXIHqnegConditionalReductionActual
import tmp.sheaf.xif.paper.Mzk1StepXIHqnegCoercionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi discharged hqneg gate

Derives hqneg from the paper q-reading negativity and discharges it into the final
Cor 3.12 acceptance (hqneg is no longer a free hypothesis at the call site). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIDischargedGateV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIHqnegConditionalReductionActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIHqnegCoercionActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_discharged_gate (R : PaperKummerReading T)
    (h : R.qReading < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T R
        (stepxi_hqneg_of_qReading_neg T R h) ipl hipl she hshe apt hapt) :=
  stepxi_hqneg_conditional_cor312 T R h ipl hipl she hshe apt hapt

#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIDischargedGateV2Actual.stepxi_discharged_gate

end LeanFormal.IUT.XiFPaper.Mzk1StepXIDischargedGateV2Actual

end
