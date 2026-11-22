import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import LeanFormal.IUT.IUTIII.Corollary312.Comparison
import LeanFormal.IUT.IUTIII.Corollary312.Routes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Mzk1HullStepXIContractConsumerTreeActualAdapted — StepXI contract tree consumer

A472/A473: real Lean consumer over the tree StepXI contract/comparison/route
wrappers. No sorry/axioms; conditional on a supplied contract; no closure
claim. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullStepXIContractConsumerTreeActualAdapted

open LeanFormal.IUT

theorem stepXIContractTree_cor312 (contract : StepXIContract) :
    Cor312Conclusion contract := cor312Conclusion_of_contract contract

theorem stepXIContractTree_route (route : Cor312Route) (contract : StepXIContract) :
    Cor312Conclusion ({ route := route, contract := contract } : Cor312RouteCertificate).contract :=
  ({ route := route, contract := contract } : Cor312RouteCertificate).conclusion

theorem stepXIContractTree_qpositive (contract : StepXIContract) :
    0 < -contract.qSigned := q_positive_of_constructed_stepXI contract

def stepXIContractTreeRows : List (String × String × String) :=
  [ ("contract -> Cor312", "PROVED", "stepXIContractTree_cor312"),
    ("route certificate", "PROVED", "stepXIContractTree_route"),
    ("q-positive", "PROVED", "stepXIContractTree_qpositive") ]

theorem stepXIContractTreeRows_length : stepXIContractTreeRows.length = 3 := rfl

#check stepXIContractTree_cor312
#check stepXIContractTreeRows_length

end LeanFormal.IUT.XiFPaper.Mzk1HullStepXIContractConsumerTreeActualAdapted
end