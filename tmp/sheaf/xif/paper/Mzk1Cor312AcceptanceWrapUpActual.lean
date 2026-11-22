/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceGreenSummaryActual
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceV2Actual
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceV4Actual

/-!
# A577 Cor 3.12 acceptance wrap-up (mainline lane)

Final packaging of the mainline-owned acceptance artifacts:
* generic interface conclusions (`acceptance_summary_standard` in the green summary);
* readings conclusions (`acceptance_summary_readings`);
* the explicit-instance conclusions from V2/V4.

Axiom evidence is recorded by the qpilot-owned axiom-gate evidence package
(`Mzk1ABCStage5AxiomGateActual`); this file is a statement-level wrap-up only.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceWrapUpActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceGreenSummaryActual

variable {α : Type*} {vol : Set α → ℝ}

/-- **Cor 3.12 acceptance (standard path, wrap-up)**: Cor 3.12 conclusion, strict
  paper inequality, and `C_Theta >= -1`, from any green xi-e requirement. -/
theorem cor312_acceptance (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (requirementContract D hqneg ipl hipl she hshe apt hapt) ∧
      (requirementSignedQ D < requirementSignedTheta D) ∧
      (∀ C : ℝ,
        requirementSignedTheta D ≤ C * (-requirementSignedQ D) → -1 ≤ C) :=
  acceptance_summary_standard D hqneg ipl hipl she hshe apt hapt

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **Acceptance readings (wrap-up)**: paper statement plus finiteness. -/
theorem cor312_acceptance_readings
    (R : LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual.PaperKummerReading T) :
    R.thetaReading ≥ R.qReading ∧
      (∃ qLog thetaLog : ℝ, qLog = R.qReading ∧ thetaLog = R.thetaReading) :=
  acceptance_summary_readings T R

end LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceWrapUpActual

end
