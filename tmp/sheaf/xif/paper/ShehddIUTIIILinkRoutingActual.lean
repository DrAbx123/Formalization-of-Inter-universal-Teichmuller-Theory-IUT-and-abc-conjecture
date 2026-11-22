import tmp.sheaf.xif.paper.Mzk1IUTIIILinkActual
import tmp.sheaf.xif.paper.Mzk1Cor312TargetWiringActual

/-!
# ShehddIUTIIILinkRoutingActual — typed IUTII->IUTIII link drives the Cor 3.12 route wiring

STEP 0 prior-art (reuse, no new math):
* Mzk1IUTIIILinkActual: IUTIIToStepXILink (real SourceLogShellDatum + explicit ipl/she/apt
  evidence) -> StepXIContract -> Cor312Conclusion / q-pilot positivity (PROVED consumers);
* Mzk1Cor312TargetWiringActual: route certificate from a StepXIContract and the three
  recorded Cor312Route labels, all giving Cor312Conclusion (PROVED consumers).

This file only COMPOSES the two existing consumers: the typed IUTII link is fed into the
three-route wiring.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddIUTIIILinkRoutingActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312TargetWiringActual

/-- Wrapper: the contract carried by a typed IUTII->IUTIII link. -/
def iutiiLinkContract (L : IUTIIToStepXILink) : StepXIContract := L.toContract

/-- **PROVED composition:** the typed IUTII->IUTIII link satisfies the Cor 3.12
conclusion and the q-pilot positivity through its StepXI contract. -/
theorem iutiiLink_conclusion_and_positivity (L : IUTIIToStepXILink) :
    Cor312Conclusion L.toContract ∧ 0 < -L.toContract.qSigned :=
  ⟨cor312Conclusion_of_IUTIIToStepXILink L, q_positive_of_IUTIIToStepXILink L⟩

/-- **PROVED composition:** the typed IUTII->IUTIII link, fed through the three recorded
Cor 3.12 routes, yields Cor 3.12 for every route certificate. -/
theorem iutiiLink_allRoutes (L : IUTIIToStepXILink) :
    Cor312Conclusion (certificateOfContract Cor312Route.mochizuki3115 L.toContract).contract ∧
      Cor312Conclusion (certificateOfContract Cor312Route.arithmeticTeichmuller L.toContract).contract ∧
        Cor312Conclusion (certificateOfContract Cor312Route.sarkisyanErdosKac L.toContract).contract :=
  all_routes_conclusion L.toContract

/-- **PROVED composition:** any route certificate built from the link's contract yields
Cor 3.12 (certificate projection). -/
theorem iutiiLink_routeCertificate_conclusion (L : IUTIIToStepXILink)
    (route : Cor312Route) : Cor312Conclusion (certificateOfContract route L.toContract).contract :=
  certificate_conclusion (certificateOfContract route L.toContract)

/-- Row record: what is reused vs composed here. -/
def iutiiLinkRoutingRows : List (String × String × String) :=
  [ ("typed IUTII->IUTIII link => StepXI contract", "REUSED PROVED", "Mzk1IUTIIILinkActual.IUTIIToStepXILink.toContract")
  , ("link => Cor 3.12 conclusion + q positivity", "REUSED PROVED", "cor312Conclusion_of_IUTIIToStepXILink, q_positive_of_IUTIIToStepXILink")
  , ("contract => route certificate (3 routes)", "REUSED PROVED", "Mzk1Cor312TargetWiringActual.certificateOfContract")
  , ("link => all-routes Cor 3.12 conclusions", "COMPOSED PROVED", "iutiiLink_allRoutes")
  , ("link => per-route certificate conclusion", "COMPOSED PROVED", "iutiiLink_routeCertificate_conclusion")
  , ("ipl/she/apt paper content derived from IUTII", "NAMED", "carried as explicit evidence fields in IUTIIToStepXILink; not derived") ]

theorem iutiiLinkRoutingRows_length : iutiiLinkRoutingRows.length = 6 := rfl

#check iutiiLink_conclusion_and_positivity
#check iutiiLink_allRoutes
#check iutiiLink_routeCertificate_conclusion
#check iutiiLinkRoutingRows_length

end LeanFormal.IUT.XiFPaper.ShehddIUTIIILinkRoutingActual
end
