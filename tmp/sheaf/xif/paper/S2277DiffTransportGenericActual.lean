import tmp.sheaf.xif.paper.S2266DiffProductReindexActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2277DiffTransportGenericActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2215TransversalTransportActual
open LeanFormal.IUT.XiFPaper.S2226TransferProductActual
open LeanFormal.IUT.XiFPaper.S2266DiffProductReindexActual

universe u

theorem S2277_map_bridge {G G' : Type u} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) : H.map (e : G →* G') = H.map e.toMonoidHom := rfl

/-- Standalone generic diff-transport statement. -/
def S2277DiffTransportGenericRequired : Prop :=
  ∀ {G G' : Type u} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) (S T : H.LeftTransversal) [Subgroup.FiniteIndex H]
    [(H.map e.toMonoidHom).FiniteIndex]
    (A : Type u) [CommGroup A] (ϕ : H →* A)
    (ϕ' : H.map e.toMonoidHom →* A),
    (∀ h : H, ϕ' (Subgroup.equivMapOfInjective H e.toMonoidHom
      e.injective h) = ϕ h) →
    Subgroup.leftTransversals.diff ϕ'
      (S2215TransversalTransport e H S)
      (S2215TransversalTransport e H T) =
      Subgroup.leftTransversals.diff ϕ S T

#check S2277_map_bridge
#check S2277DiffTransportGenericRequired

end LeanFormal.IUT.XiFPaper.S2277DiffTransportGenericActual

end