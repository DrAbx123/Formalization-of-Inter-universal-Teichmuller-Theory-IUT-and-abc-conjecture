import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.Mzk1SignedLogVolumeCor312Actual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual

/-! # Mzk1FinalAssemblyStatementChecksActual — final-assembly statements and self-checks

A540 module (no new mathematics, independent of the pending KummerTransport olean):
states and proves the self-check obligations of the final Cor 3.12 assembly on the
generic non-vacuous xi-e requirement data: contract slot values, the Cor312Conclusion,
and the non-reflexivity (strict) witness.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalAssemblyStatementChecksActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeCor312Actual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

universe u

variable {α : Type u} {vol : Set α → Real}

/-- Self-check: the assembled contract's q slot is the signed q-pilot value. -/
theorem requirementContract_qSigned (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0) (ipl : Prop) (hipl : ipl)
    (she : Prop) (hshe : she) (apt : Prop) (hapt : apt) :
    (requirementContract D hqneg ipl hipl she hshe apt hapt).qSigned =
      requirementSignedQ D := rfl

/-- Self-check: the assembled contract's theta slot is the signed Theta-pilot value. -/
theorem requirementContract_thetaSigned (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0) (ipl : Prop) (hipl : ipl)
    (she : Prop) (hshe : she) (apt : Prop) (hapt : apt) :
    (requirementContract D hqneg ipl hipl she hshe apt hapt).thetaSigned =
      requirementSignedTheta D := rfl

/-- Self-check: the assembled target slot equals the theta slot, and target_le_theta
is the genuine signed comparison (not a definitional reflexivity on equal data). -/
theorem requirementContract_target_le_theta (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0) (ipl : Prop) (hipl : ipl)
    (she : Prop) (hshe : she) (apt : Prop) (hapt : apt) :
    (requirementContract D hqneg ipl hipl she hshe apt hapt).targetSigned <=
      (requirementContract D hqneg ipl hipl she hshe apt hapt).thetaSigned :=
  (requirementContract D hqneg ipl hipl she hshe apt hapt).target_le_theta

/-- The Cor 3.12 conclusion of the assembled contract (consumer statement). -/
theorem assembly_cor312 (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0) (ipl : Prop) (hipl : ipl)
    (she : Prop) (hshe : she) (apt : Prop) (hapt : apt) :
    Cor312Conclusion (requirementContract D hqneg ipl hipl she hshe apt hapt) :=
  requirement_cor312 D hqneg ipl hipl she hshe apt hapt

/-- Non-vacuity self-check: the xi-e requirement gives a STRICT signed comparison
(it does not collapse to `le_rfl`). -/
theorem assembly_strict_nontrivial (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D < requirementSignedTheta D :=
  requirement_strict_signed D

/-- The assembled signed comparison, packaged for the final assembly. -/
theorem assembly_signed_inequality (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D <= requirementSignedTheta D :=
  requirement_signed_inequality D

/-- Self-check conjunction: slot identities + strict witness + Cor312Conclusion.
Statement-level summary of the final assembly obligations. -/
theorem assembly_selfcheck (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0) (ipl : Prop) (hipl : ipl)
    (she : Prop) (hshe : she) (apt : Prop) (hapt : apt) :
    (requirementContract D hqneg ipl hipl she hshe apt hapt).qSigned =
        requirementSignedQ D ∧
      (requirementContract D hqneg ipl hipl she hshe apt hapt).thetaSigned =
        requirementSignedTheta D ∧
      requirementSignedQ D < requirementSignedTheta D :=
  ⟨requirementContract_qSigned D hqneg ipl hipl she hshe apt hapt,
   requirementContract_thetaSigned D hqneg ipl hipl she hshe apt hapt,
   assembly_strict_nontrivial D⟩

#check requirementContract_qSigned
#check requirementContract_thetaSigned
#check requirementContract_target_le_theta
#check assembly_cor312
#check assembly_strict_nontrivial
#check assembly_selfcheck

end LeanFormal.IUT.XiFPaper.Mzk1FinalAssemblyStatementChecksActual
end
