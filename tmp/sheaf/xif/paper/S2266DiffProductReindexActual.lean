import tmp.sheaf.xif.paper.S2242DiffProductActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2266DiffProductReindexActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2215TransversalTransportActual
open LeanFormal.IUT.XiFPaper.S2226TransferProductActual
open LeanFormal.IUT.XiFPaper.S2233TransferProductProofActual
open LeanFormal.IUT.XiFPaper.S2242DiffProductActual
open Subgroup.leftTransversals

universe u

noncomputable def S2266DiffTerm {G : Type u} [Group G] (H : Subgroup G)
    (S T : H.LeftTransversal) (q : Quotient (QuotientGroup.leftRel H)) : H :=
  ⟨(S.2.leftQuotientEquiv q : G)⁻¹ * (T.2.leftQuotientEquiv q : G),
    QuotientGroup.leftRel_apply.mp <| Quotient.exact' <|
      (S.2.leftQuotientEquiv.symm_apply_apply q).trans
        (T.2.leftQuotientEquiv.symm_apply_apply q).symm⟩

noncomputable def S2266DiffExplicit {G : Type u} [Group G] (H : Subgroup G)
    (S T : H.LeftTransversal) [Fintype (Quotient (QuotientGroup.leftRel H))]
    (A : Type u) [CommGroup A] (ϕ : H →* A) : A :=
  ∏ q : Quotient (QuotientGroup.leftRel H), ϕ (S2266DiffTerm H S T q)

theorem S2266_diff_explicit {G : Type u} [Group G] (H : Subgroup G)
    (S T : H.LeftTransversal) [Subgroup.FiniteIndex H]
    (A : Type u) [CommGroup A] (ϕ : H →* A) :
    letI := H.fintypeQuotientOfFiniteIndex
    diff ϕ S T = S2266DiffExplicit H S T A ϕ := by
  letI := H.fintypeQuotientOfFiniteIndex
  rw [Subgroup.leftTransversals.diff]
  rfl

/-- Exact missing remaining diff product invariance. -/
abbrev S2266DiffInvarianceRequired : Prop :=
  S2226DiffTransportRequired.{u}

#check S2266_diff_explicit
#check S2266DiffInvarianceRequired
#print axioms S2266_diff_explicit

end LeanFormal.IUT.XiFPaper.S2266DiffProductReindexActual

end