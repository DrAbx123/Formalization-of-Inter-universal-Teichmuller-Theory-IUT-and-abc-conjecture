import tmp.sheaf.xif.paper.S2215TransversalTransportActual

-- S2226: transfer product invariance exact surface.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2226TransferProductActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2215TransversalTransportActual
open Subgroup.leftTransversals

universe u

/-- Exact missing: diff/transfer product invariance under the transported
transversal. -/
def S2226DiffTransportRequired : Prop :=
  ∀ {G G' : Type u} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) (S T : H.LeftTransversal) [Subgroup.FiniteIndex H]
    [Subgroup.FiniteIndex (H.map e.toMonoidHom)]
    (A : Type u) [CommGroup A] (ϕ : H →* A)
    (ϕ' : H.map e.toMonoidHom →* A),
    (∀ h : H, ϕ' (Subgroup.equivMapOfInjective H e.toMonoidHom
      e.injective h) = ϕ h) →
    diff ϕ' (S2215TransversalTransport e H S)
      (S2215TransversalTransport e H T) = diff ϕ S T

/-- Exact missing quotient-left-coset reindexing API, which would feed the
diff product calculation. -/
def S2226LeftCosetReindexRequired : Prop :=
  ∀ {G G' : Type u} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G),
    Nonempty ((Quotient (QuotientGroup.leftRel H)) ≃
      (Quotient (QuotientGroup.leftRel (H.map e.toMonoidHom))))

#check S2226DiffTransportRequired
#check S2226LeftCosetReindexRequired

end LeanFormal.IUT.XiFPaper.S2226TransferProductActual

end