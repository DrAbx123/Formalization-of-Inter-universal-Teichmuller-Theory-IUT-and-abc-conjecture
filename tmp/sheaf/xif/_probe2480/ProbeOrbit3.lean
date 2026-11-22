import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual

noncomputable section
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
namespace ProbeOrbit3
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual

example (σ : Equiv.Perm S2056Root) :
    (letI := Classical.decEq S2056Root; σ.cycleType) = σ.cycleType := by
  have h : (Classical.decEq S2056Root) = (fun a b => Subtype.instDecidableEq a b) :=
    Subsingleton.elim _ _
  rw [h]

example (σ : Equiv.Perm S2056Root) :
    orbitSizeMultiset σ = σ.cycleType +
      Multiset.replicate (Fintype.card (Function.fixedPoints σ)) 1 := by
  have h : (Classical.decEq S2056Root) = (fun a b => Subtype.instDecidableEq a b) :=
    Subsingleton.elim _ _
  unfold orbitSizeMultiset
  rw [h]

example (σ : Equiv.Perm S2056Root) (hσ : σ.cycleType = ({10,2} : Multiset ℕ)) :
    orbitSizeMultiset σ = ({10,2} : Multiset ℕ) := by
  have hcard : Fintype.card S2056Root = 12 := by
    rw [← Nat.card_eq_fintype_card, S2056Root_card]
  have hfix : Fintype.card (Function.fixedPoints σ) = 0 := by
    rw [Equiv.Perm.card_fixedPoints, hcard, hσ]
    norm_num
  have h : (Classical.decEq S2056Root) = (fun a b => Subtype.instDecidableEq a b) :=
    Subsingleton.elim _ _
  unfold orbitSizeMultiset
  rw [h, hσ, hfix, Multiset.replicate_zero, add_zero]

example (σ : Equiv.Perm S2056Root)
    (hσ : orbitSizeMultiset σ = ({10,2} : Multiset ℕ)) :
    σ.cycleType = ({10,2} : Multiset ℕ) := by
  have h : (Classical.decEq S2056Root) = (fun a b => Subtype.instDecidableEq a b) :=
    Subsingleton.elim _ _
  have hσ' := hσ
  unfold orbitSizeMultiset at hσ'
  rw [h] at hσ'
  have hfix : Fintype.card (Function.fixedPoints σ) = 0 := by
    by_contra hne
    have hpos : 0 < Fintype.card (Function.fixedPoints σ) := Nat.pos_of_ne_zero hne
    have hmem : (1 : ℕ) ∈ σ.cycleType +
        Multiset.replicate (Fintype.card (Function.fixedPoints σ)) 1 :=
      Multiset.mem_add.mpr (Or.inr (Multiset.mem_replicate.mpr ⟨hne, rfl⟩))
    rw [hσ'] at hmem
    norm_num at hmem
  rw [hfix, Multiset.replicate_zero, add_zero] at hσ'
  exact hσ'

end ProbeOrbit3
end
