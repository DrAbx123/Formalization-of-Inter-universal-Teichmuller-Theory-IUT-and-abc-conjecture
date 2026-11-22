import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import LeanFormal.IUT.IUTIII.Corollary312.Routes
import LeanFormal.IUT.IUTIII.Corollary312.Comparison

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: IUTIII.COR312.TARGET wiring (DAG node iutiii:IUTIII.COR312.TARGET; 1 unproved dep) -> tree modules: StepXI/Contract.lean (StepXIContract:32, Cor312Conclusion:46, cor312_of_constructed_stepXI:49, q_positive_of_constructed_stepXI:53), Routes.lean (Cor312Route:32, Cor312RouteCertificate:38, .conclusion:42), Comparison.lean (cor312Conclusion_of_contract:7) -> paper-layer typed consumer wiring; no new math, no closure.

# Mzk1Cor312TargetWiringActual — paper-layer consumer wiring for the Cor 3.12 target node

PROVED wiring (tree theorems consumed):
* `certificateOfContract`: route + StepXI contract -> Cor312RouteCertificate;
* `certificate_conclusion`: Cor312RouteCertificate.conclusion;
* `mochizuki_route_conclusion`: Cor312Conclusion from a contract;
* `q_positive_target`: qSigned < 0 consequence;
* route compatibility: constructing certificates for the three recorded routes.
The conditional content is the StepXIContract itself (tree field: contract construction
from IUT source data is the named item), not re-proved.  Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312TargetWiringActual

open LeanFormal.IUT

/-- A route certificate from a route label and a StepXI contract. -/
def certificateOfContract (route : Cor312Route) (contract : StepXIContract) :
    Cor312RouteCertificate :=
  { route := route, contract := contract }

/-- **PROVED:** every route certificate yields Cor 3.12 via the contract. -/
theorem certificate_conclusion (certificate : Cor312RouteCertificate) :
    Cor312Conclusion certificate.contract :=
  certificate.conclusion

/-- **PROVED:** a StepXI contract yields Cor 3.12 (tree Comparison wrapper). -/
theorem mochizuki_route_conclusion (contract : StepXIContract) :
    Cor312Conclusion contract :=
  cor312Conclusion_of_contract contract

/-- **PROVED:** the q-pilot sign consequence of a contract. -/
theorem q_positive_target (contract : StepXIContract) :
    0 < -contract.qSigned :=
  q_positive_of_constructed_stepXI contract

/-- The three recorded routes all yield certificates from the same contract. -/
theorem all_routes_conclusion (contract : StepXIContract) :
    Cor312Conclusion (certificateOfContract Cor312Route.mochizuki3115 contract).contract ∧
      Cor312Conclusion (certificateOfContract Cor312Route.arithmeticTeichmuller contract).contract ∧
      Cor312Conclusion (certificateOfContract Cor312Route.sarkisyanErdosKac contract).contract :=
  ⟨mochizuki_route_conclusion contract, mochizuki_route_conclusion contract,
    mochizuki_route_conclusion contract⟩

/-- Rows: what the paper-layer consumer proves vs the named contract construction. -/
def cor312TargetWiringRows : List (String × String × String) :=
  [ ("route certificate from contract", "PROVED", "certificateOfContract (tree Cor312RouteCertificate)")
  , ("certificate => Cor 3.12", "PROVED", "certificate_conclusion / tree Routes.lean:42")
  , ("contract => Cor 3.12 (Comparison wrapper)", "PROVED", "mochizuki_route_conclusion / tree Comparison.lean:7")
  , ("q-pilot positivity from contract", "PROVED", "q_positive_target / tree Contract.lean:53")
  , ("all three routes yield Cor 3.12 from one contract", "PROVED", "all_routes_conclusion")
  , ("construct StepXIContract from IUT source data", "NAMED (tree)", "tree Contract.lean:61 stepXIContractConstruction is an Obligation; construction unfinished") ]

theorem cor312TargetWiringRows_length : cor312TargetWiringRows.length = 6 := rfl

#check certificateOfContract
#check certificate_conclusion
#check mochizuki_route_conclusion
#check all_routes_conclusion
#check cor312TargetWiringRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Cor312TargetWiringActual
end