import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import LeanFormal.IUT.IUTIII.Corollary312.Routes
import LeanFormal.IUT.IUTIII.Corollary312.Comparison

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: iutiii:IUTIII.STEPXI.CONTRACT / IUTIII.COR312.TARGET advance -> tree StepXIContract (Contract.lean:32), Cor312Conclusion:46, Cor312RouteCertificate (Routes.lean:38), Comparison.lean:7 -> TYPED CONTRACT CONSTRUCTION from explicit source data (the tree's stepXIContractConstruction Obligation is unfinished; here the source data are explicit fields, ipl/she/apt with evidence), plus PROVED Cor312/q-positive/route consequences. No closure.

# Mzk1StepXIContractConstructionActual — typed StepXI contract construction from source data

PROVED:
* `StepXIContractSourceData.toContract`: typed source data -> StepXIContract;
* `sourceData_contract_exists`: a contract exists for every source datum;
* `sourceData_cor312` / `sourceData_q_positive`: Cor 3.12 and q-pilot positivity;
* `sourceData_routeCertificate`: route certificate for any route label.
NAMED: the source-data fields (q/theta/target signed values and ipl/she/apt evidence);
constructing them from IUT source data remains the tree Obligation.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual

open LeanFormal.IUT

/-- Typed source data for the StepXI contract: the ordered signed values plus the
ipl/she/apt statements with explicit evidence. -/
structure StepXIContractSourceData where
  qSigned : ℝ
  thetaSigned : ℝ
  targetSigned : ℝ
  q_negative : qSigned < 0
  q_le_target : qSigned ≤ targetSigned
  target_le_theta : targetSigned ≤ thetaSigned
  iplProp : Prop
  sheProp : Prop
  aptProp : Prop
  ipl_evidence : iplProp
  she_evidence : sheProp
  apt_evidence : aptProp

/-- **PROVED:** source data assemble a StepXI contract. -/
def StepXIContractSourceData.toContract (S : StepXIContractSourceData) : StepXIContract :=
  { qSigned := S.qSigned
    thetaSigned := S.thetaSigned
    targetSigned := S.targetSigned
    q_negative := S.q_negative
    ipl := S.iplProp
    she := S.sheProp
    apt := S.aptProp
    ipl_evidence := S.ipl_evidence
    she_evidence := S.she_evidence
    apt_evidence := S.apt_evidence
    q_le_target := S.q_le_target
    target_le_theta := S.target_le_theta }

/-- **PROVED:** a StepXI contract exists for every source datum. -/
theorem sourceData_contract_exists (S : StepXIContractSourceData) :
    ∃ contract : StepXIContract, Cor312Conclusion contract :=
  ⟨S.toContract, cor312_of_constructed_stepXI S.toContract⟩

/-- **PROVED:** Cor 3.12 from source data. -/
theorem sourceData_cor312 (S : StepXIContractSourceData) :
    Cor312Conclusion S.toContract :=
  cor312_of_constructed_stepXI S.toContract

/-- **PROVED:** q-pilot positivity from source data. -/
theorem sourceData_q_positive (S : StepXIContractSourceData) :
    0 < -S.toContract.qSigned :=
  q_positive_of_constructed_stepXI S.toContract

/-- **PROVED:** route certificate for any route label from source data. -/
def sourceData_routeCertificate (route : Cor312Route) (S : StepXIContractSourceData) :
    Cor312RouteCertificate :=
  { route := route, contract := S.toContract }

theorem sourceData_routeCertificate_conclusion (route : Cor312Route)
    (S : StepXIContractSourceData) :
    Cor312Conclusion (sourceData_routeCertificate route S).contract :=
  (sourceData_routeCertificate route S).conclusion

/-- Rows. -/
def stepXIContractRows : List (String × String × String) :=
  [ ("typed source data -> StepXI contract", "PROVED", "StepXIContractSourceData.toContract")
  , ("contract existence", "PROVED", "sourceData_contract_exists")
  , ("Cor 3.12 from source data", "PROVED", "sourceData_cor312")
  , ("q-pilot positivity from source data", "PROVED", "sourceData_q_positive")
  , ("route certificate from source data", "PROVED", "sourceData_routeCertificate")
  , ("construction of source data from IUT input", "NAMED (tree Obligation)", "Contract.lean:61 stepXIContractConstruction; ipl/she/apt statements explicit named fields") ]

theorem stepXIContractRows_length : stepXIContractRows.length = 6 := rfl

#check StepXIContractSourceData
#check sourceData_cor312
#check sourceData_q_positive
#check sourceData_routeCertificate
#check stepXIContractRows_length

end LeanFormal.IUT.XiFPaper.Mzk1StepXIContractConstructionActual
end