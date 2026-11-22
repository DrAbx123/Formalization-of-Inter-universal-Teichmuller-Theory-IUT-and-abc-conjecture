import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-! # Mzk1AxiomGateActual — axiom gate: restated claims + axiom printouts

A547 gate module: restates (re-derives) the key Cor 3.12 assembly claims so the watchdog
log carries a compile-time gate, and prints the axiom dependencies of the core theorems
for audit (`#print axioms`): expected only `propext`, `Classical.choice`, `Quot.sound`
(plus no `sorryAx`).  No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AxiomGateActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

universe u

variable {α : Type u} {vol : Set α → Real}

/-- Gate: non-vacuous xi-e data yields the strict signed comparison. -/
theorem gate_strict (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D < requirementSignedTheta D :=
  requirement_strict_signed D

/-- Gate: non-vacuous xi-e data yields the signed inequality. -/
theorem gate_inequality (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D <= requirementSignedTheta D :=
  requirement_signed_inequality D

/-- Gate: the assembly yields the Cor 3.12 conclusion. -/
theorem gate_cor312 (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0) (ipl : Prop) (hipl : ipl)
    (she : Prop) (hshe : she) (apt : Prop) (hapt : apt) :
    Cor312Conclusion (requirementContract D hqneg ipl hipl she hshe apt hapt) :=
  requirement_cor312 D hqneg ipl hipl she hshe apt hapt

/-- Gate: the contract target slot is the Theta-pilot signed value. -/
theorem gate_target (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0) (ipl : Prop) (hipl : ipl)
    (she : Prop) (hshe : she) (apt : Prop) (hapt : apt) :
    (requirementContract D hqneg ipl hipl she hshe apt hapt).targetSigned =
      requirementSignedTheta D :=
  rfl

#print axioms gate_strict
#print axioms gate_inequality
#print axioms gate_cor312
#print axioms gate_target

#check gate_strict
#check gate_inequality
#check gate_cor312
#check gate_target

end LeanFormal.IUT.XiFPaper.Mzk1AxiomGateActual
end
