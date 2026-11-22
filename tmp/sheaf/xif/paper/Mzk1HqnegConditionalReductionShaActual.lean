import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.Mzk1ResolvedRequirementAcceptanceShaActual

/-!
# shehdd A602 hqneg conditional reduction (clean gate companion)

`hqneg : requirementSignedQ D < 0` is an explicit HYPOTHESIS of the resolved
chain.  This file records the clean conditional reduction:
* `hqneg_conditional_cor312`: given `hqneg` and real IPL/SHE/APT evidence, the
  requirement contract satisfies `Cor312Conclusion`;
* `hqneg_conditional_strict`: the non-vacuous xi-e strict inequality (always,
  independent of `hqneg`);
* `hqneg_gate_clean`: a Prop bundling the two, with both proofs.

Non-derivability of `hqneg` from the other requirement fields is an audit
observation (requires a concrete requirement whose q reading is `log 2 > 0`);
it is NOT claimed here.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1HqnegConditionalReductionShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

theorem hqneg_conditional_cor312 {α : Type} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (requirementContract D hqneg ipl hipl she hshe apt hapt) :=
  requirement_cor312 D hqneg ipl hipl she hshe apt hapt

theorem hqneg_conditional_strict {α : Type} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D < requirementSignedTheta D :=
  requirement_strict_signed D

/-- Clean hqneg gate: for every requirement and every real qualitative evidence,
the conjunction of the strict requirement inequality and the conditional
`Cor312Conclusion` holds, with `hqneg` an explicit hypothesis. -/
theorem hqneg_gate_clean {α : Type} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    (requirementSignedQ D < requirementSignedTheta D) ∧
      Cor312Conclusion (requirementContract D hqneg ipl hipl she hshe apt hapt) :=
  ⟨requirement_strict_signed D,
    requirement_cor312 D hqneg ipl hipl she hshe apt hapt⟩

end LeanFormal.IUT.XiFPaper.Mzk1HqnegConditionalReductionShaActual
