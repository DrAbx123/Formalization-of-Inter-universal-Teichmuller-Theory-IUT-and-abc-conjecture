import tmp.sheaf.xif.paper.S2266DiffProductReindexActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2282DiffTermRewriteActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2215TransversalTransportActual
open LeanFormal.IUT.XiFPaper.S2226TransferProductActual
open LeanFormal.IUT.XiFPaper.S2233TransferProductProofActual
open LeanFormal.IUT.XiFPaper.S2242DiffProductActual
open LeanFormal.IUT.XiFPaper.S2266DiffProductReindexActual
open Subgroup.leftTransversals

universe u

theorem S2282_term_eq
    {G G' : Type u} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) (S T : H.LeftTransversal)
    (A : Type u) [CommGroup A] (ϕ : H →* A)
    (ϕ' : H.map e.toMonoidHom →* A)
    (hϕ : ∀ h : H, ϕ' (Subgroup.equivMapOfInjective H e.toMonoidHom
      e.injective h) = ϕ h)
    (q : Quotient (QuotientGroup.leftRel H)) :
    ϕ' (S2266DiffTerm (H.map e.toMonoidHom)
      (S2215TransversalTransport e H S)
      (S2215TransversalTransport e H T)
      (S2233LeftCosetReindex e H q)) =
      ϕ (S2266DiffTerm H S T q) := by
  have hα := S2242_transport_leftQuotientEquiv e H S q
  have hβ := S2242_transport_leftQuotientEquiv e H T q
  have hsub :
      S2266DiffTerm (H.map e.toMonoidHom)
        (S2215TransversalTransport e H S)
        (S2215TransversalTransport e H T)
        (S2233LeftCosetReindex e H q) =
      Subgroup.equivMapOfInjective H e.toMonoidHom e.injective
        (S2266DiffTerm H S T q) := by
    ext
    simp only [S2266DiffTerm, Subgroup.coe_equivMapOfInjective_apply]
    rw [hα, hβ]
    simp [map_mul, map_inv]

  rw [hsub, hϕ]


theorem S2282_diff_explicit_transport
    {G G' : Type u} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) (S T : H.LeftTransversal) [Subgroup.FiniteIndex H]
    [(H.map e.toMonoidHom).FiniteIndex]
    (A : Type u) [CommGroup A] (ϕ : H →* A)
    (ϕ' : H.map e.toMonoidHom →* A)
    (hϕ : ∀ h : H, ϕ' (Subgroup.equivMapOfInjective H e.toMonoidHom
      e.injective h) = ϕ h) :
    letI := H.fintypeQuotientOfFiniteIndex
    letI := (H.map e.toMonoidHom).fintypeQuotientOfFiniteIndex
    S2266DiffExplicit (H.map e.toMonoidHom)
      (S2215TransversalTransport e H S)
      (S2215TransversalTransport e H T) A ϕ' =
      S2266DiffExplicit H S T A ϕ := by
  letI := H.fintypeQuotientOfFiniteIndex
  letI := (H.map e.toMonoidHom).fintypeQuotientOfFiniteIndex
  rw [S2266DiffExplicit, S2266DiffExplicit]
  refine Finset.prod_bij
    (fun q' (_ : q' ∈ Finset.univ) => (S2233LeftCosetReindex e H).symm q')
    ?_ ?_ ?_ ?_
  · intro q' _; exact Finset.mem_univ _
  · intro q₁ _ q₂ _ h
    exact (S2233LeftCosetReindex e H).symm.injective h
  · intro q _; exact ⟨S2233LeftCosetReindex e H q, Finset.mem_univ _,
      Equiv.symm_apply_apply (S2233LeftCosetReindex e H) q⟩
  · intro q' _
    have hq : S2233LeftCosetReindex e H
        ((S2233LeftCosetReindex e H).symm q') = q' := Equiv.apply_symm_apply _ q'
    rw [← hq]
    simpa only [Equiv.symm_apply_apply] using
      S2282_term_eq e H S T A ϕ ϕ' hϕ
        ((S2233LeftCosetReindex e H).symm q')

theorem S2282_diff_transport
    {G G' : Type u} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) (S T : H.LeftTransversal) [Subgroup.FiniteIndex H]
    [(H.map e.toMonoidHom).FiniteIndex]
    (A : Type u) [CommGroup A] (ϕ : H →* A)
    (ϕ' : H.map e.toMonoidHom →* A)
    (hϕ : ∀ h : H, ϕ' (Subgroup.equivMapOfInjective H e.toMonoidHom
      e.injective h) = ϕ h) :
    diff ϕ' (S2215TransversalTransport e H S)
      (S2215TransversalTransport e H T) = diff ϕ S T := by
  letI := H.fintypeQuotientOfFiniteIndex
  letI := (H.map e.toMonoidHom).fintypeQuotientOfFiniteIndex
  rw [S2266_diff_explicit H S T A ϕ]
  rw [S2266_diff_explicit (H.map e.toMonoidHom)
    (S2215TransversalTransport e H S)
    (S2215TransversalTransport e H T) A ϕ']
  exact S2282_diff_explicit_transport e H S T A ϕ ϕ' hϕ


theorem S2282_diff_transport_required : S2226DiffTransportRequired.{u} := by
  intro G G' instG instG' e H S T instH instH' A instA phi phi' hphi
  exact S2282_diff_transport e H S T A phi phi' hphi

#check S2282_diff_transport_required
#print axioms S2282_diff_transport_required

#check S2282_diff_transport
#print axioms S2282_diff_transport

#check S2282_term_eq
#print axioms S2282_term_eq

end LeanFormal.IUT.XiFPaper.S2282DiffTermRewriteActual

end