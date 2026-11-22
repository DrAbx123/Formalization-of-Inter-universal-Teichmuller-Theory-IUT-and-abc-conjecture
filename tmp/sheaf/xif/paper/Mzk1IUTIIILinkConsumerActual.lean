import tmp.sheaf.xif.paper.Mzk1IUTIIILinkActual
import LeanFormal.IUT.IUTIII.Corollary312.Routes
import LeanFormal.IUT.IUTIII.Corollary312.Comparison

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: typed IUTII->IUTIII link (Mzk1IUTIIILinkActual) + tree route certificates (Routes.lean:32-47, Comparison.lean:7) -> paper-layer consumer: link => contract => route certificates for all three routes => Cor312Conclusion; q-pilot positivity. No new math; no closure.

# Mzk1IUTIIILinkConsumerActual — route harness on the typed IUTII link

PROVED:
* `routeCertificate_of_link`: the typed link + route label gives a Cor312RouteCertificate;
* `routeConclusion_of_link`: its Cor 3.12 conclusion;
* `allRoutes_of_link`: all three recorded routes yield Cor 3.12 from one link.
NAMED: ipl/she/apt statements carried inside the link (explicit Props with evidence).
Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual

/-- **PROVED:** the typed IUTII->IUTIII link yields a route certificate. -/
def routeCertificate_of_link (route : Cor312Route) (L : IUTIIToStepXILink) :
    Cor312RouteCertificate :=
  { route := route, contract := L.toContract }

/-- **PROVED:** Cor 3.12 from a link and a route label. -/
theorem routeConclusion_of_link (route : Cor312Route) (L : IUTIIToStepXILink) :
    Cor312Conclusion (routeCertificate_of_link route L).contract :=
  (routeCertificate_of_link route L).conclusion

/-- **PROVED:** all three routes yield Cor 3.12 from one link. -/
theorem allRoutes_of_link (L : IUTIIToStepXILink) :
    Cor312Conclusion (routeCertificate_of_link Cor312Route.mochizuki3115 L).contract ∧
      Cor312Conclusion (routeCertificate_of_link Cor312Route.arithmeticTeichmuller L).contract ∧
      Cor312Conclusion (routeCertificate_of_link Cor312Route.sarkisyanErdosKac L).contract :=
  ⟨routeConclusion_of_link _ L, routeConclusion_of_link _ L, routeConclusion_of_link _ L⟩

/-- Rows: proved harness vs named link content. -/
def linkConsumerRows : List (String × String × String) :=
  [ ("link => route certificate", "PROVED", "routeCertificate_of_link")
  , ("link + route => Cor 3.12", "PROVED", "routeConclusion_of_link")
  , ("all three routes from one link", "PROVED", "allRoutes_of_link")
  , ("ipl/she/apt statements", "NAMED (link fields)", "explicit Props with evidence inside IUTIIToStepXILink; not derived from IUTII")
  , ("StepXIContract construction from IUT source data", "NAMED (tree Obligation)", "Contract.lean:61 stepXIContractConstruction") ]

theorem linkConsumerRows_length : linkConsumerRows.length = 5 := rfl

#check routeCertificate_of_link
#check routeConclusion_of_link
#check allRoutes_of_link
#check linkConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkConsumerActual
end