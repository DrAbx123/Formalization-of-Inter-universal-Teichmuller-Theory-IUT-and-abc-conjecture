import LeanFormal.IUT.IUTIII.Corollary312.Comparison
import LeanFormal.IUT.IUTIII.Corollary312.Routes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: tree-only Cor312 comparison facts -> Comparison.cor312Conclusion_of_contract:7 + Routes.Cor312RouteCertificate(.conclusion):38/42 + Contract Cor312Conclusion/q_positive -> PROVED tree facts: contract conclusion, route certificate conclusion, q-pilot positivity, all-routes conclusion. No extra ports; no closure.

# Mzk1TreeCor312ComparisonActual — tree-only Cor 3.12 comparison facts

PROVED: contract conclusion; route certificate conclusion; q-positive; all-routes
conclusion.  Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual

open LeanFormal.IUT

theorem tree_contract_cor312 (contract : StepXIContract) :
    Cor312Conclusion contract := cor312Conclusion_of_contract contract

theorem tree_route_cor312 (route : Cor312Route) (contract : StepXIContract) :
    Cor312Conclusion ({ route := route, contract := contract } : Cor312RouteCertificate).contract :=
  ({ route := route, contract := contract } : Cor312RouteCertificate).conclusion

theorem tree_q_positive (contract : StepXIContract) : 0 < -contract.qSigned :=
  q_positive_of_constructed_stepXI contract

theorem tree_all_routes_cor312 (contract : StepXIContract) :
    Cor312Conclusion ({ route := Cor312Route.mochizuki3115, contract := contract } : Cor312RouteCertificate).contract ∧
      Cor312Conclusion ({ route := Cor312Route.arithmeticTeichmuller, contract := contract } : Cor312RouteCertificate).contract ∧
      Cor312Conclusion ({ route := Cor312Route.sarkisyanErdosKac, contract := contract } : Cor312RouteCertificate).contract :=
  ⟨tree_route_cor312 _ contract, tree_route_cor312 _ contract, tree_route_cor312 _ contract⟩

def treeCor312Rows : List (String × String × String) :=
  [ ("contract conclusion", "PROVED", "tree_contract_cor312 (Comparison:7)")
  , ("route certificate conclusion", "PROVED", "tree_route_cor312 (Routes:42)")
  , ("q-pilot positivity", "PROVED", "tree_q_positive (Contract:53)")
  , ("all-routes conclusion", "PROVED", "tree_all_routes_cor312")
  , ("contract construction from IUT input", "NAMED", "Contract:61 Obligation") ]

theorem treeCor312Rows_length : treeCor312Rows.length = 5 := rfl

#check tree_contract_cor312
#check tree_route_cor312
#check tree_all_routes_cor312
#check treeCor312Rows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ComparisonActual
end