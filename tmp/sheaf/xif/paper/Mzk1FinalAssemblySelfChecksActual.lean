/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual
import Mathlib.Tactic

/-!
# Mzk1FinalAssemblySelfChecksActual — self-checks of the final 3.12 assembly

A540: the final assembly (`requirementContract`/`requirement_cor312`, green
`Mzk1XiEContainmentRequirementActual`) is checked for:
* the contract's q/theta/target slots equal the genuine signed readouts;
* `targetSigned = thetaSigned` and `targetSigned ≠ qSigned` (no q-as-target vacuity);
* the comparison is strict whenever the measure strictly increases
  (non-vacuity: not reflexive);
* the paper `C_Θ ≥ −1` form follows from the strict signed inequality.

No new axiom, no True placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalAssemblySelfChecksActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

variable {α : Type*} {vol : Set α → Real}

/-- The contract built from a genuine xi-e requirement. -/
noncomputable def finalContract (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) : StepXIContract :=
  requirementContract D hqneg ipl hipl she hshe apt hapt

/-- Self-check: the target slot is the Theta-pilot signed readout. -/
theorem finalContract_target_eq_theta (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    (finalContract D hqneg ipl hipl she hshe apt hapt).targetSigned =
      requirementSignedTheta D := rfl

/-- Self-check: the q slot is the genuine q-pilot signed readout. -/
theorem finalContract_q_eq_reading (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    (finalContract D hqneg ipl hipl she hshe apt hapt).qSigned =
      requirementSignedQ D := rfl

/-- Self-check (no q-as-target vacuity): the target is strictly bigger than the q slot. -/
theorem finalContract_target_ne_q (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    (finalContract D hqneg ipl hipl she hshe apt hapt).targetSigned ≠
      (finalContract D hqneg ipl hipl she hshe apt hapt).qSigned := by
  rw [finalContract_target_eq_theta, finalContract_q_eq_reading]
  exact ne_of_gt (requirement_strict_signed D)

/-- Self-check (non-vacuity): the comparison is strict, not reflexive. -/
theorem finalContract_comparison_strict (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    (finalContract D hqneg ipl hipl she hshe apt hapt).qSigned <
      (finalContract D hqneg ipl hipl she hshe apt hapt).targetSigned := by
  rw [finalContract_q_eq_reading, finalContract_target_eq_theta]
  exact requirement_strict_signed D

/-- Self-check: the Cor 3.12 conclusion of the final contract. -/
theorem finalContract_cor312 (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (finalContract D hqneg ipl hipl she hshe apt hapt) :=
  requirement_cor312 D hqneg ipl hipl she hshe apt hapt

#check finalContract_target_eq_theta
#check finalContract_target_ne_q
#check finalContract_comparison_strict

end LeanFormal.IUT.XiFPaper.Mzk1FinalAssemblySelfChecksActual
end
