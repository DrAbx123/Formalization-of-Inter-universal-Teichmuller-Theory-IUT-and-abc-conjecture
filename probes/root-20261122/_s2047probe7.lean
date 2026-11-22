import tmp.sheaf.xif.paper.S2027LocalArtinActual

noncomputable section
open scoped DirectSum commutatorElement
open LeanFormal.IUT
open LeanFormal.IUT.LocalMLFModelTMPair
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2011Cor110bActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2024LocalReciprocityActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual

namespace LeanFormal.IUT.XiFPaper.S2047GeneralLocalCFTActual

variable (p : Nat) [Fact (Nat.Prime p)] (U : Index p)

noncomputable def normSubgroup (M : IntermediateField (localField p U) (AlgebraicClosure ℚ_[p])) :
    Subgroup (localField p U)ˣ :=
  Subgroup.map (Units.map (Algebra.norm (localField p U) : M →* localField p U)) ⊤

theorem mem_normSubgroup {M : IntermediateField (localField p U) (AlgebraicClosure ℚ_[p])}
    {x : (localField p U)ˣ} :
    x ∈ normSubgroup p U M ↔ ∃ y : Mˣ, Units.map (Algebra.norm (localField p U)) y = x := by
  simp [normSubgroup]

theorem normSubgroup_antitone {M N : IntermediateField (localField p U) (AlgebraicClosure ℚ_[p])}
    (h : M ≤ N) : normSubgroup p U N ≤ normSubgroup p U M := by
  letI : Algebra M N := RingHom.toAlgebra (IntermediateField.inclusion h).toRingHom
  haveI : IsScalarTower (localField p U) M N := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  intro x hx
  rw [mem_normSubgroup] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨Units.map (Algebra.norm M) y, ?_⟩
  apply Units.ext
  change Algebra.norm (localField p U) ((Algebra.norm M) (y : ↥N)) = Algebra.norm (localField p U) (y : ↥N)
  exact Algebra.norm_norm (R := localField p U) (S := M) (A := N) (a := (y : ↥N))

end LeanFormal.IUT.XiFPaper.S2047GeneralLocalCFTActual
