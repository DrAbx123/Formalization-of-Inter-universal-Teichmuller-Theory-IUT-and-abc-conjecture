import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual

noncomputable section
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
namespace ProbeOrbit
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual

example (σ : Equiv.Perm S2056Root) :
    orbitSizeMultiset σ = σ.cycleType +
      Multiset.replicate (Fintype.card (Function.fixedPoints σ)) 1 := by
  classical
  rfl

example (σ : Equiv.Perm S2056Root) (hσ : σ.cycleType = ({10,2} : Multiset ℕ)) :
    orbitSizeMultiset σ = ({10,2} : Multiset ℕ) := by
  classical
  have hcard : Fintype.card S2056Root = 12 := by
    rw [← Nat.card_eq_fintype_card, S2056Root_card]
  have hfix : Fintype.card (Function.fixedPoints σ) = 0 := by
    rw [Equiv.Perm.card_fixedPoints, hcard, hσ]
    norm_num
  simp only [orbitSizeMultiset, hσ, hfix, Multiset.replicate_zero, add_zero]

example (σ : Equiv.Perm S2056Root)
    (hσ : orbitSizeMultiset σ = ({10,2} : Multiset ℕ)) :
    σ.cycleType = ({10,2} : Multiset ℕ) := by
  classical
  have hfix : Fintype.card (Function.fixedPoints σ) = 0 := by
    by_contra h
    have hpos : 0 < Fintype.card (Function.fixedPoints σ) := Nat.pos_of_ne_zero h
    have hmem : (1 : ℕ) ∈ orbitSizeMultiset σ := by
      simp only [orbitSizeMultiset]
      exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_replicate.mpr ⟨h, rfl⟩))
    rw [hσ] at hmem
    norm_num at hmem
  simp only [orbitSizeMultiset, hfix, Multiset.replicate_zero, add_zero] at hσ
  exact hσ

end ProbeOrbit
end
