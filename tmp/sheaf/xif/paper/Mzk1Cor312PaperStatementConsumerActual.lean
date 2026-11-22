/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-!
# A543 paper-statement consumer of the xi-e requirement (chain-independent)

Consumes the green `XiEContainmentRequirement` (non-vacuous xi-e interface with
`strict_measure`) and produces, for arbitrary real `(IPL)/(SHE)/(APT)` evidence:
* the `Cor312Conclusion` (green signed StepXI route),
* the paper statement shape `qSigned <= thetaSigned`,
* the `C_Theta >= -1` form,
* the STRICT signed inequality `qSigned < thetaSigned` from `strict_measure`.

No dependency on the Kummer chain; the final assembly instantiates the requirement
with the realized PaperKummerReading.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperStatementConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

variable {α : Type*} {vol : Set α → ℝ}

/-- The consumer's StepXI contract from the xi-e requirement. -/
noncomputable def consumerContract (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) : StepXIContract :=
  requirementContract D hqneg ipl hipl she hshe apt hapt

/-- The Cor 3.12 conclusion from the consumer contract. -/
theorem consumer_cor312 (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (consumerContract D hqneg ipl hipl she hshe apt hapt) :=
  requirement_cor312 D hqneg ipl hipl she hshe apt hapt

/-- The paper statement shape: `qSigned <= thetaSigned`. -/
theorem consumer_paper_shape (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D ≤ requirementSignedTheta D :=
  requirement_signed_inequality D

/-- **Strict paper inequality** `qSigned < thetaSigned` (non-vacuity from
  `strict_measure`). -/
theorem consumer_paper_strict (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D < requirementSignedTheta D :=
  requirement_strict_signed D

/-- The `C_Theta >= -1` form from a `C-Theta` bound (with the explicit negativity
  hypothesis on the signed q reading, i.e. paper's `|log q| > 0`). -/
theorem consumer_CTheta_ge_neg_one (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0) {C : ℝ}
    (hC : requirementSignedTheta D ≤ C * (-requirementSignedQ D)) : -1 ≤ C := by
  have hqpos : 0 < -requirementSignedQ D := neg_pos.mpr hqneg
  have hle : requirementSignedQ D ≤ requirementSignedTheta D :=
    requirement_signed_inequality D
  have h1 : requirementSignedQ D ≤ C * (-requirementSignedQ D) :=
    le_trans hle hC
  have h2 : requirementSignedQ D / (-requirementSignedQ D) ≤ C :=
    (div_le_iff₀ hqpos).mpr h1
  have h3 : requirementSignedQ D / (-requirementSignedQ D) = -1 := by
    have hne : requirementSignedQ D ≠ 0 := ne_of_lt hqneg
    calc requirementSignedQ D / (-requirementSignedQ D) = -(requirementSignedQ D / requirementSignedQ D) := by rw [div_neg]
      _ = -(1 : ℝ) := by rw [div_self hne]
      _ = -1 := by ring
  rw [h3] at h2
  linarith

end

end LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperStatementConsumerActual
-- A543 retry after transient missing mathlib private olean.
