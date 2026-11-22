import tmp.sheaf.xif.paper.Mzk1StepXIAuditProofActual
import tmp.sheaf.xif.paper.Mzk1StepXIHqnegCoercionActual
import tmp.sheaf.xif.paper.Mzk1StepXIGateVerificationActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi A618 machine-proof consumer

Green-only consumer of the A618 audit proof/gate; avoids the red owner file
`Mzk1A618MachineProofActual`. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIA618MachineProofConsumerV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIGateVerificationActual
open LeanFormal.IUT.XiFPaper.Mzk1StepXIHqnegCoercionActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem stepxi_a618_machine_proof (R : PaperKummerReading T)
    (h : R.qReading < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T R
        (stepxi_hqneg_of_qReading_neg T R h) ipl hipl she hshe apt hapt) :=
  stepxi_gate_verification T R h ipl hipl she hshe apt hapt

end LeanFormal.IUT.XiFPaper.Mzk1StepXIA618MachineProofConsumerV2Actual

end
