/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-!
# A565 stable acceptance INTERFACE (green modules only)

Provides the generic acceptance interface from the green
`XiEContainmentRequirement`: for ANY xi-e requirement (regardless of how the
geometry/scaling resolves `strict_measure`), plus real `(IPL)/(SHE)/(APT)` evidence,
one obtains the Cor 3.12 `Cor312Conclusion`; the signed lower/upper readings are the
requirement's signed q/Theta values.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceInterfaceActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

variable {α : Type*} {vol : Set α → ℝ}

/-- Generic acceptance: the green `requirement_cor312` gives `Cor312Conclusion` for
  arbitrary real evidence. -/
theorem acceptance_cor312 (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract D hqneg ipl hipl she hshe apt hapt) :=
  requirement_cor312 D hqneg ipl hipl she hshe apt hapt

/-- The acceptance's signed paper inequality. -/
theorem acceptance_paper_inequality (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D ≤ requirementSignedTheta D :=
  requirement_signed_inequality D

/-- The acceptance's STRICT signed paper inequality (non-vacuity of xi-e). -/
theorem acceptance_paper_inequality_strict (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D < requirementSignedTheta D :=
  requirement_strict_signed D

/-- The paper `C_Theta >= -1` form: if the Theta reading is bounded by `C * (-q)`, then
  `-1 <= C`. -/
theorem acceptance_CTheta (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0) {C : ℝ}
    (hC : requirementSignedTheta D ≤ C * (-requirementSignedQ D)) : -1 ≤ C := by
  have hqpos : 0 < -requirementSignedQ D := neg_pos.mpr hqneg
  have hle : requirementSignedQ D ≤ requirementSignedTheta D :=
    requirement_signed_inequality D
  have h1 : requirementSignedQ D ≤ C * (-requirementSignedQ D) :=
    le_trans hle hC
  have h2 : requirementSignedQ D / (-requirementSignedQ D) ≤ C :=
    (div_le_iff₀ hqpos).mpr h1
  have hne : requirementSignedQ D ≠ 0 := ne_of_lt hqneg
  have h3 : requirementSignedQ D / (-requirementSignedQ D) = -1 := by
    calc requirementSignedQ D / (-requirementSignedQ D)
        = -(requirementSignedQ D / requirementSignedQ D) := by rw [div_neg]
      _ = -(1 : ℝ) := by rw [div_self hne]
      _ = -1 := by ring
  rw [h3] at h2
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceInterfaceActual
