/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.Mzk1HqnegCleanGateQpilotActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual

/-! # Mzk1HqnegConditionalReductionQpilotActual — hqneg conditional reduction

A602 (qpilot lane): the final assembly reduced to the single `hqneg` hypothesis:
supplying `requirementSignedQ (requirementOfReading T R) < 0` yields the whole
Cor 3.12 contract/conclusion without further inputs.  (Discharging `hqneg` itself
is the hull/mainline `Mzk1Hqneg*` model task.) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HqnegConditionalReductionQpilotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1HqnegCleanGateQpilotActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (R : PaperKummerReading T)

/-- Conditional reduction: `hqneg` alone yields the Cor 3.12 conclusion of the
assembled final contract. -/
theorem hqneg_conditional_conclusion
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (cor312Contract_final T R hqneg ipl hipl she hshe apt hapt) :=
  cor312Conclusion_final T R hqneg ipl hipl she hshe apt hapt

/-- Conditional reduction in `∃` form: `hqneg` alone yields some Cor 3.12 contract
with `Cor312Conclusion`. -/
theorem hqneg_conditional_exists
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    ∃ C : StepXIContract, Cor312Conclusion C :=
  ⟨cor312Contract_final T R hqneg ipl hipl she hshe apt hapt,
   cor312Conclusion_final T R hqneg ipl hipl she hshe apt hapt⟩

/-- The reduction as a function of the `hqneg` witness. -/
theorem hqneg_reduction_function (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    (requirementSignedQ (requirementOfReading T R) < 0) →
      ∃ C : StepXIContract, Cor312Conclusion C :=
  fun hqneg =>
    hqneg_conditional_exists T R hqneg (SHEArrowStatement T)
      (sheArrowStatement_proved T) she hshe apt hapt

#check hqneg_conditional_conclusion
#check hqneg_conditional_exists

end LeanFormal.IUT.XiFPaper.Mzk1HqnegConditionalReductionQpilotActual
end
