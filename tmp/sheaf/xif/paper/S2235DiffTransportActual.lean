import tmp.sheaf.xif.paper.S2233TransferProductProofActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2235DiffTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2215TransversalTransportActual
open LeanFormal.IUT.XiFPaper.S2226TransferProductActual
open LeanFormal.IUT.XiFPaper.S2233TransferProductProofActual

universe u

/-- Exact missing: the transported transversal represents the conjugated
representative in the reindexed left coset. -/
def S2235TransportLeftQuotientRequired : Prop :=
  ∀ {G G' : Type u} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) (S : H.LeftTransversal)
    (q : Quotient (QuotientGroup.leftRel H)),
    ((S2215TransversalTransport e H S).2.leftQuotientEquiv
        (S2233LeftCosetReindex e H q) : G') =
      e ((S.2.leftQuotientEquiv q : G))

/-- Exact diff product invariance target. -/
abbrev S2235DiffTransportRequired : Prop :=
  S2226DiffTransportRequired.{u}

#check S2235TransportLeftQuotientRequired
#check S2235DiffTransportRequired

end LeanFormal.IUT.XiFPaper.S2235DiffTransportActual

end