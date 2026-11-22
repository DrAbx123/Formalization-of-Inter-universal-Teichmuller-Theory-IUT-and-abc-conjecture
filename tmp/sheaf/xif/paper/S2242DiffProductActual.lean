import tmp.sheaf.xif.paper.S2235DiffTransportActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2242DiffProductActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2215TransversalTransportActual
open LeanFormal.IUT.XiFPaper.S2226TransferProductActual
open LeanFormal.IUT.XiFPaper.S2233TransferProductProofActual
open LeanFormal.IUT.XiFPaper.S2235DiffTransportActual

universe u

theorem S2242_reindex_mk {G G' : Type u} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G) (x : G) :
    S2233LeftCosetReindex e H (Quotient.mk'' x) =
      Quotient.mk'' (e x) :=
  rfl

theorem S2242_transport_leftQuotientEquiv
    {G G' : Type u} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) (S : H.LeftTransversal)
    (q : Quotient (QuotientGroup.leftRel H)) :
    ((S2215TransversalTransport e H S).2.leftQuotientEquiv
        (S2233LeftCosetReindex e H q) : G') =
      e ((S.2.leftQuotientEquiv q : G)) := by
  let S' := S2215TransversalTransport e H S
  let b : ↥(S'.1) := ⟨e (S.2.leftQuotientEquiv q), by
    change e (S.2.leftQuotientEquiv q) ∈ e '' (S : Set G)
    exact ⟨(S.2.leftQuotientEquiv q : G), (S.2.leftQuotientEquiv q).2, rfl⟩⟩
  have ha : Quotient.mk'' ((S'.2.leftQuotientEquiv
      (S2233LeftCosetReindex e H q)) : G') =
      S2233LeftCosetReindex e H q :=
    S'.2.leftQuotientEquiv.symm_apply_apply _
  have hb : Quotient.mk'' (b : G') = S2233LeftCosetReindex e H q := by
    change Quotient.mk'' (e (S.2.leftQuotientEquiv q)) = _
    rw [← S2242_reindex_mk e H (S.2.leftQuotientEquiv q)]
    congr 1
    exact S.2.leftQuotientEquiv.symm_apply_apply q
  have hsub : S'.2.leftQuotientEquiv (S2233LeftCosetReindex e H q) = b := by
    apply S'.2.leftQuotientEquiv.symm.injective
    rw [S'.2.leftQuotientEquiv.symm_apply_apply]
    exact hb.symm
  exact congrArg Subtype.val hsub

#check S2242_transport_leftQuotientEquiv
#print axioms S2242_transport_leftQuotientEquiv

end LeanFormal.IUT.XiFPaper.S2242DiffProductActual

end