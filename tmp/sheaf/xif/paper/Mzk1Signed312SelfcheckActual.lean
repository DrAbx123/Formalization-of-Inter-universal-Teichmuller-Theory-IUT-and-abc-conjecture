import tmp.sheaf.xif.paper.Mzk1Signed312AssemblyActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-! # Mzk1Signed312SelfcheckActual — signed 3.12 self-checks against the current assembly

A543 self-check module (no new mathematics): concrete witnesses for the signed
Corollary 3.12 comparison and its constant form, using the current
StepXIContract assembly and the Gogopex Stage1Comparison bridge.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Signed312SelfcheckActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Signed312AssemblyActual

/-- Signed comparison witness: qSigned = -2 <= thetaSigned = -1. -/
def witnessContract : StepXIContract where
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

/-- Self-check: the witness contract gives the signed Cor 3.12 inequality. -/
theorem witness_signed_inequality :
    -witnessContract.thetaSigned <= -witnessContract.qSigned :=
  corollary312Inequality_of_contract witnessContract

/-- Self-check: the witness contract satisfies the printed inequality values. -/
theorem witness_values :
    witnessContract.qSigned = -2 ∧ witnessContract.thetaSigned = -1 := by
  norm_num [witnessContract]

/-- Self-check: the Gogopex Stage1Comparison package exists for the witness. -/
theorem witness_stage1_comparison :
    0 < (stage1ComparisonOfContract witnessContract).q.value :=
  (stage1ComparisonOfContract witnessContract).q_positive

/-- Self-check: converse direction: signed inequality gives the contract comparison. -/
theorem converse_comparison {thetaSigned qSigned : Real}
    (h : -thetaSigned <= -qSigned) : qSigned <= thetaSigned :=
  contract_comparison_of_signedInequality h

#check witness_signed_inequality
#check witness_values
#check witness_stage1_comparison
#check converse_comparison

end LeanFormal.IUT.XiFPaper.Mzk1Signed312SelfcheckActual
end
