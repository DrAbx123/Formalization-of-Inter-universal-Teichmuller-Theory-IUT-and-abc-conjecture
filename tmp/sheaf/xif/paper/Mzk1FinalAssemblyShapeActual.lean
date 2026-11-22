import tmp.sheaf.xif.paper.Mzk1Signed312AssemblyActual

/-! # Mzk1FinalAssemblyShapeActual — paper Cor 3.12 shape statements

A543 module (no new mathematics): paper-shaped statement of IUT III Corollary 3.12
(signed q/Theta comparison with negative q-pilot) and its relation to the current
StepXIContract / Gogopex Stage1Comparison assembly.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalAssemblyShapeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Signed312AssemblyActual

/-- The paper shape of the Corollary 3.12 conclusion (IUT III 10324-10353):
the signed q-pilot value is negative and at most the signed Theta-pilot value. -/
def Paper312Shape (qSigned thetaSigned : Real) : Prop :=
  qSigned < 0 ∧ qSigned <= thetaSigned

/-- A StepXI contract satisfies the paper shape at its q/theta slots. -/
theorem paperShape_of_contract (C : StepXIContract) :
    Paper312Shape C.qSigned C.thetaSigned :=
  ⟨C.q_negative, le_trans C.q_le_target C.target_le_theta⟩

/-- The signed Cor 3.12 inequality from a contract. -/
theorem signedInequality_of_contract (C : StepXIContract) :
    -C.thetaSigned <= -C.qSigned :=
  corollary312Inequality_of_contract C

/-- The paper shape is exactly the pair (negativity, comparison). -/
theorem paperShape_iff (qSigned thetaSigned : Real) :
    Paper312Shape qSigned thetaSigned ↔
      qSigned < 0 ∧ qSigned <= thetaSigned :=
  Iff.rfl

/-- Concrete non-vacuous contract witness for the paper shape. -/
def exampleContract : StepXIContract where
  qSigned := -2
  thetaSigned := -1
  targetSigned := -2
  q_negative := by norm_num
  ipl := True
  she := True
  apt := True
  ipl_evidence := trivial
  she_evidence := trivial
  apt_evidence := trivial
  q_le_target := by norm_num
  target_le_theta := by norm_num

/-- The concrete witness satisfies the paper shape (non-vacuity self-check). -/
theorem paperShape_example : Paper312Shape exampleContract.qSigned exampleContract.thetaSigned :=
  paperShape_of_contract exampleContract

/-- Constant form at the witness: `thetaSigned / (-qSigned) = 1/2 >= -1`. -/
theorem cTheta_example : -1 <= exampleContract.thetaSigned / (-exampleContract.qSigned) := by
  norm_num [exampleContract]

#check Paper312Shape
#check paperShape_of_contract
#check signedInequality_of_contract
#check paperShape_example
#check cTheta_example

end LeanFormal.IUT.XiFPaper.Mzk1FinalAssemblyShapeActual
end
