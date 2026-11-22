/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HqnegCleanGateQpilotActual
import tmp.sheaf.xif.paper.Mzk1HqnegConditionalReductionQpilotActual
import tmp.sheaf.xif.paper.Mzk1ABCEstimatesArithmeticQpilotActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual

/-! # Mzk1HqnegGateSummaryQpilotActual — hqneg gate summary (A605)

Thin summary of the hqneg gate: the clean axiom gate and the conditional
reduction (hqneg is the single remaining hypothesis; discharge is hull/mainline)
together with the two-estimates arithmetic hooks. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HqnegGateSummaryQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1HqnegCleanGateQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1HqnegConditionalReductionQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCEstimatesArithmeticQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (R : PaperKummerReading T)

/-- hqneg gate: with the discharged `hqneg` hypothesis the assembly conclusion is
available. -/
theorem hqnegGate_conclusion
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T R hqneg ipl hipl she hshe apt hapt) :=
  hqneg_conditional_conclusion T R hqneg ipl hipl she hshe apt hapt

/-- hqneg gate summary: conclusion from `hqneg` and the two-estimates arithmetic
chain are both available. -/
theorem hqnegGate_summary
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (she : Prop) (hshe : she) (apt : Prop) (hapt : apt) :
    (∃ C : StepXIContract, Cor312Conclusion C) ∧
      (∀ {h v w t D eps : Real}, 0 ≤ eps → eps ≤ 1 → 0 ≤ w →
        h ≤ (1 + eps) * v → v ≤ (1 + eps) * w + t + D →
        h ≤ (1 + 3 * eps) * w + (1 + eps) * (t + D)) :=
  ⟨hqneg_conditional_exists T R hqneg (SHEArrowStatement T)
      (sheArrowStatement_proved T) she hshe apt hapt,
   fun h0 h1 hw hge1 hge2 =>
     height_le_absorbed h0 h1 hw (height_le_of_twoEstimates h0 hge1 hge2)⟩

#check hqnegGate_summary

end LeanFormal.IUT.XiFPaper.Mzk1HqnegGateSummaryQpilotActual
end
