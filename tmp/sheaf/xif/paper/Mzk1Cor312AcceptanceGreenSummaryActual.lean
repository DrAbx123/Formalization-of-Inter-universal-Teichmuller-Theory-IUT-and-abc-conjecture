/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceInterfaceActual
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceV2Actual
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceV4Actual
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceShapeChecksActual

/-!
# A572 green acceptance summary (mainline lane)

Bundles the mainline-owned acceptance artifacts into a single summary theorem:
* the generic interface (`acceptance_cor312` + paper inequality + C_Theta),
* the paper readings statement (`acceptance_paper_statement` + finiteness),
* the explicit-instance conclusions (`cor312_conclusion` from V2/V4).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceGreenSummaryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceV4Actual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceShapeChecksActual

variable {α : Type*} {vol : Set α → ℝ}

/-- **Acceptance summary (standard path)**: the interface conclusions for any green
  xi-e requirement: Cor 3.12 conclusion, paper inequality (strict), C_Theta >= -1. -/
theorem acceptance_summary_standard (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (requirementContract D hqneg ipl hipl she hshe apt hapt) ∧
      (requirementSignedQ D < requirementSignedTheta D) ∧
      (∀ C : ℝ,
        requirementSignedTheta D ≤ C * (-requirementSignedQ D) → -1 ≤ C) :=
  ⟨Mzk1Cor312AcceptanceInterfaceActual.acceptance_cor312 D hqneg ipl hipl she hshe apt hapt,
   Mzk1Cor312AcceptanceInterfaceActual.acceptance_paper_inequality_strict D,
   fun C hC => Mzk1Cor312AcceptanceInterfaceActual.acceptance_CTheta D hqneg hC⟩

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **Acceptance summary (readings path)**: paper statement + finiteness. -/
theorem acceptance_summary_readings
    (R : LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual.PaperKummerReading T) :
    R.thetaReading ≥ R.qReading ∧
      (∃ qLog thetaLog : ℝ, qLog = R.qReading ∧ thetaLog = R.thetaReading) :=
  ⟨Mzk1Cor312AcceptanceShapeChecksActual.acceptance_paper_statement T R, Mzk1Cor312AcceptanceShapeChecksActual.acceptance_readings_finite T R⟩

end LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceGreenSummaryActual

end
