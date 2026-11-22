import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceFinalActual
import tmp.sheaf.xif.paper.Mzk1StepXIHqnegCoercionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi hqneg-dispatched acceptance gate

From paper q-reading negativity, dispatch the requirement-signed negative and apply
the green acceptance-final theorem. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIHqnegDispatchedAcceptanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIHqnegCoercionActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_hqneg_dispatched_acceptance (R : PaperKummerReading T)
    (h : R.qReading < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T R
        (stepxi_hqneg_of_qReading_neg T R h) ipl hipl she hshe apt hapt) :=
  acceptanceFinal_paper T R (stepxi_hqneg_of_qReading_neg T R h)
    ipl hipl she hshe apt hapt

#print axioms LeanFormal.IUT.XiFPaper.Mzk1StepXIHqnegDispatchedAcceptanceActual.stepxi_hqneg_dispatched_acceptance

end LeanFormal.IUT.XiFPaper.Mzk1StepXIHqnegDispatchedAcceptanceActual

end
