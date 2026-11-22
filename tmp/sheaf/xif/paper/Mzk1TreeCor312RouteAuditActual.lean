import LeanFormal.IUT.IUTIII.Corollary312.Routes
import LeanFormal.IUT.IUTIII.Corollary312.Comparison
import LeanFormal.IUT.IUTIII.Corollary312.Obligations

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: Cor312 route audit (iutiii:IUTIII.COR312.TARGET evidence) -> Cor312Route (Routes:32) three constructors; Cor312RouteCertificate(.conclusion):38/42; Cor312Conclusion (Contract:46); cor312Conclusion_of_contract (Comparison:7); Obligations ids -> PROVED: route enumeration, certificate conclusion, obligation ids, and stage route tags. No new math; no closure.

# Mzk1TreeCor312RouteAuditActual — Cor 3.12 route audit facts

PROVED:
* `cor312Route_enum`: every route is mochizuki3115, arithmeticTeichmuller, or
  sarkisyanErdosKac;
* `cor312_route_conclusion`: every certificate concludes Cor 3.12;
* `cor312_contract_conclusion`: every contract concludes Cor 3.12.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312RouteAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.Audit

/-- **PROVED:** Cor312Route is exhaustive (three recorded routes). -/
theorem cor312Route_enum (r : Cor312Route) :
    r = Cor312Route.mochizuki3115 ∨ r = Cor312Route.arithmeticTeichmuller ∨
      r = Cor312Route.sarkisyanErdosKac := by
  cases r with
  | mochizuki3115 => exact Or.inl rfl
  | arithmeticTeichmuller => exact Or.inr (Or.inl rfl)
  | sarkisyanErdosKac => exact Or.inr (Or.inr rfl)

/-- **PROVED:** every route certificate concludes Cor 3.12. -/
theorem cor312_route_conclusion (certificate : Cor312RouteCertificate) :
    Cor312Conclusion certificate.contract := certificate.conclusion

/-- **PROVED:** every contract concludes Cor 3.12. -/
theorem cor312_contract_conclusion (contract : StepXIContract) :
    Cor312Conclusion contract := cor312Conclusion_of_contract contract

/-- **PROVED:** the obligation ids consumed by the route. -/
theorem cor312_obligation_ids :
    ipl.id = "IUT-III.IPL" ∧ she.id = "IUT-III.SHE" ∧ apt.id = "IUT-III.APT" :=
  ⟨rfl, rfl, rfl⟩

def cor312RouteAuditRows : List (String × String × String) :=
  [ ("route enumeration", "PROVED", "cor312Route_enum (Routes:32-36)")
  , ("certificate conclusion", "PROVED", "cor312_route_conclusion (Routes:42)")
  , ("contract conclusion", "PROVED", "cor312_contract_conclusion (Comparison:7)")
  , ("obligation ids", "PROVED", "cor312_obligation_ids (Obligations:5/12/19)")
  , ("certificate construction from IUT input", "NAMED", "StepXI contract construction Obligation") ]

theorem cor312RouteAuditRows_length : cor312RouteAuditRows.length = 5 := rfl

#check cor312Route_enum
#check cor312_route_conclusion
#check cor312_obligation_ids
#check cor312RouteAuditRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312RouteAuditActual
end