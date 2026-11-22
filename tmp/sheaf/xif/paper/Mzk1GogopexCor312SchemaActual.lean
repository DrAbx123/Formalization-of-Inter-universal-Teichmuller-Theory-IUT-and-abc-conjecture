import tmp.sheaf.gogopex.Iut.Stage1.CorollarySchema
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Gogopex Cor 3.12 signed-inequality schema ↔ our StepXIContract

Real reference glue: the Gogopex `Corollary312Inequality` signed-real schema
and our `Cor312Conclusion` are two faces of the same ordered inequality.  No
statement is redefined; both definitions are imported and bridged. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GogopexCor312SchemaActual

open LeanFormal.IUT
open Iut.Stage1

/-- Our StepXI ordered conclusion as the Gogopex signed-real schema. -/
theorem gogopexCorollary312_of_contract (contract : StepXIContract) :
    Corollary312Inequality
      (signedPilotLogVolume PilotSide.theta contract.thetaSigned)
      (signedPilotLogVolume PilotSide.q contract.qSigned) :=
  corollary312_of_signed_le (cor312_of_constructed_stepXI contract)

/-- A StepXI contract read as the Gogopex signed-real comparison data. -/
def comparisonDataOfContract (contract : StepXIContract) :
    Corollary312ComparisonData where
  thetaSigned := contract.thetaSigned
  qSigned := contract.qSigned
  q_positive := q_positive_of_constructed_stepXI contract
  qSigned_le_thetaSigned := cor312_of_constructed_stepXI contract

theorem comparisonDataOfContract_corollary312 (contract : StepXIContract) :
    Corollary312Inequality
      (comparisonDataOfContract contract).thetaPilot
      (comparisonDataOfContract contract).qPilot :=
  (comparisonDataOfContract contract).corollary312

/-- Conversely, the Gogopex signed schema yields a StepXI contract with the
target field unified with the Theta side (the ordered endpoint is unchanged). -/
def contractOfComparisonData (data : Corollary312ComparisonData) :
    StepXIContract where
  qSigned := data.qSigned
  thetaSigned := data.thetaSigned
  targetSigned := data.thetaSigned
  q_negative := neg_pos.mp data.q_positive
  ipl := True
  she := True
  apt := True
  ipl_evidence := trivial
  she_evidence := trivial
  apt_evidence := trivial
  q_le_target := data.qSigned_le_thetaSigned
  target_le_theta := le_rfl

theorem contractOfComparisonData_conclusion (data : Corollary312ComparisonData) :
    Cor312Conclusion (contractOfComparisonData data) :=
  cor312_of_constructed_stepXI (contractOfComparisonData data)

/-- Both schemas hold simultaneously for the same Gogopex comparison data. -/
theorem gogopex_and_cor312Conclusion (data : Corollary312ComparisonData) :
    Corollary312Inequality data.thetaPilot data.qPilot ∧
      Cor312Conclusion (contractOfComparisonData data) :=
  ⟨data.corollary312, contractOfComparisonData_conclusion data⟩

end LeanFormal.IUT.XiFPaper.Mzk1GogopexCor312SchemaActual

end
