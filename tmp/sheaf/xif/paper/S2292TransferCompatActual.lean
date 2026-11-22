import tmp.sheaf.xif.paper.S2282DiffTermRewriteActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2292TransferCompatActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2215TransversalTransportActual
open LeanFormal.IUT.XiFPaper.S2226TransferProductActual
open LeanFormal.IUT.XiFPaper.S2233TransferProductProofActual
open LeanFormal.IUT.XiFPaper.S2282DiffTermRewriteActual
open Subgroup.leftTransversals

universe u

theorem S2292_map_diff {G : Type u} [Group G] (H : Subgroup G)
    {A B : Type u} [CommGroup A] [CommGroup B] (ψ : A →* B)
    (ϕ : H →* A) (S T : H.LeftTransversal) [H.FiniteIndex] :
    ψ (diff ϕ S T) = diff (ψ.comp ϕ) S T := by
  rw [Subgroup.leftTransversals.diff, Subgroup.leftTransversals.diff]
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro q _
  rfl

theorem S2292_transport_smul {G G' : Type u} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G) (S : H.LeftTransversal) (g : G) :
    S2215TransversalTransport e H (g • S) =
      (e g) • S2215TransversalTransport e H S := by
  apply Subtype.ext
  ext x
  simp only [S2215TransversalTransport, Set.mem_image, Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    exact ⟨e z, ⟨z, hz, rfl⟩, by
      change e g * e z = e (g * z)
      rw [map_mul]⟩
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    exact ⟨g * z, ⟨z, hz, rfl⟩, by
      change e (g * z) = e g * e z
      rw [map_mul]⟩


theorem S2292_transferAb_natural {G G' : Type u} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G) (T : H.LeftTransversal)
    [Subgroup.FiniteIndex H] [(H.map e.toMonoidHom).FiniteIndex]
    (g : G) :
    Abelianization.map (Subgroup.equivMapOfInjective H e.toMonoidHom
        e.injective).toMonoidHom
        (Verlagerung.transferAb H (Abelianization.of g)) =
      Verlagerung.transferAb (H.map e.toMonoidHom)
        (Abelianization.of (e g)) := by
  let eH : H ≃* H.map e.toMonoidHom :=
    Subgroup.equivMapOfInjective H e.toMonoidHom e.injective
  let T' : (H.map e.toMonoidHom).LeftTransversal :=
    S2215TransversalTransport e H T
  have hsm : S2215TransversalTransport e H (g • T) = (e g) • T' :=
    S2292_transport_smul e H T g
  rw [Verlagerung.transferAb_of_eq_diff H T g]
  rw [Verlagerung.transferAb_of_eq_diff (H.map e.toMonoidHom) T' (e g)]
  rw [← hsm]
  rw [S2292_map_diff H (Abelianization.map eH.toMonoidHom)
    (Abelianization.of (G := H)) T (g • T)]
  exact (S2282_diff_transport e H T (g • T)
    (Abelianization (H.map e.toMonoidHom))
    ((Abelianization.map eH.toMonoidHom).comp
      (Abelianization.of (G := H)))
    (Abelianization.of (G := H.map e.toMonoidHom))
    (fun h => (Abelianization.map_of eH.toMonoidHom h).symm)).symm

#check S2292_transferAb_natural
#print axioms S2292_transferAb_natural

#check S2292_map_diff
#check S2292_transport_smul
#print axioms S2292_transport_smul

end LeanFormal.IUT.XiFPaper.S2292TransferCompatActual

end