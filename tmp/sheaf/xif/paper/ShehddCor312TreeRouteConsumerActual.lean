import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import LeanFormal.IUT.IUTIII.Corollary312.Routes
import LeanFormal.IUT.IUTIII.Corollary312.Comparison

/-!
# ShehddCor312TreeRouteConsumerActual — Cor 3.12 tree route-certificate consumer

STEP 0 prior-art (reuse only; tree modules, no paper-layer file):
* StepXI/Contract.lean: StepXIContract, Cor312Conclusion, cor312_of_constructed_stepXI,
  q_positive_of_constructed_stepXI;
* Routes.lean: Cor312Route, Cor312RouteCertificate, Cor312RouteCertificate.conclusion;
* Comparison.lean: cor312Conclusion_of_contract.

This file gives a tree-only consumer for the three recorded Cor 3.12 routes: every route
certificate built from a contract concludes Cor 3.12, and every route yields the
q-pilot positivity consequence.  No new assumptions, no sorry/axiom; the contract
construction from IUT source data remains the tree named Obligation.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddCor312TreeRouteConsumerActual

open LeanFormal.IUT

/-- **PROVED consumer:** a route certificate built from a StepXI contract concludes
Cor 3.12. -/
theorem routeCertificate_conclusion (route : Cor312Route) (contract : StepXIContract) :
    Cor312Conclusion ({ route := route, contract := contract } : Cor312RouteCertificate).contract :=
  Cor312RouteCertificate.conclusion

/-- **PROVED consumer:** the three recorded routes all conclude Cor 3.12 from the same
contract. -/
theorem threeRoutes_conclusion (contract : StepXIContract) :
    Cor312Conclusion ({ route := Cor312Route.mochizuki3115, contract := contract } :
      Cor312RouteCertificate).contract ∧
    Cor312Conclusion ({ route := Cor312Route.arithmeticTeichmuller,
      contract := contract } : Cor312RouteCertificate).contract ∧
    Cor312Conclusion ({ route := Cor312Route.sarkisyanErdosKac,
      contract := contract } : Cor312RouteCertificate).contract :=
  ⟨routeCertificate_conclusion Cor312Route.mochizuki3115 contract,
    routeCertificate_conclusion Cor312Route.arithmeticTeichmuller contract,
    routeCertificate_conclusion Cor312Route.sarkisyanErdosKac contract⟩

/-- **PROVED consumer:** a contract also gives the q-pilot positivity consequence. -/
theorem contract_q_pilot_positive (contract : StepXIContract) :
    0 < -contract.qSigned :=
  q_positive_of_constructed_stepXI contract

/-- **PROVED consumer:** a contract gives Cor 3.12 through the Comparison wrapper. -/
theorem contract_conclusion (contract : StepXIContract) :
    Cor312Conclusion contract :=
  cor312Conclusion_of_contract contract

/-- Row record: reused tree route assets vs the consumer interface. -/
def cor312TreeRouteRows : List (String × String × String) :=
  [ ("route certificate => Cor 3.12", "REUSED PROVED", "Routes.lean Cor312RouteCertificate.conclusion")
  , ("contract => Cor 3.12 (Comparison wrapper)", "REUSED PROVED", "Comparison.lean cor312Conclusion_of_contract")
  , ("contract => q-pilot positivity", "REUSED PROVED", "Contract.lean q_positive_of_constructed_stepXI")
  , ("three routes conclude from one contract", "COMPOSED PROVED", "threeRoutes_conclusion")
  , ("contract construction from IUT source data", "NAMED (tree Obligation)", "Contract.lean stepXIContractConstruction") ]

theorem cor312TreeRouteRows_length : cor312TreeRouteRows.length = 5 := rfl

#check routeCertificate_conclusion
#check threeRoutes_conclusion
#check contract_q_pilot_positive
#check cor312TreeRouteRows_length

end LeanFormal.IUT.XiFPaper.ShehddCor312TreeRouteConsumerActual
end
