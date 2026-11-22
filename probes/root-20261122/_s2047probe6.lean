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

example : IsGalois (localField p U) (AlgebraicClosure ℚ_[p]) := inferInstance

theorem fixingSubgroup_normal_of_le_maximalAbelianExtension
    (M : IntermediateField (localField p U) (AlgebraicClosure ℚ_[p]))
    (hM : M ≤ maximalAbelianExtension p U) : M.fixingSubgroup.Normal := by
  rw [← Subgroup.commutator_top_left_le_iff]
  refine le_trans (Subgroup.commutator_mono le_rfl le_top) ?_
  have h := IntermediateField.fixingSubgroup_antitone hM
  rw [fixingSubgroup_maximalAbelianExtension] at h
  exact le_trans (Subgroup.le_topologicalClosure (commutator (localGaloisGroup p U))) h

theorem normal_of_le_maximalAbelianExtension
    (M : IntermediateField (localField p U) (AlgebraicClosure ℚ_[p]))
    (hM : M ≤ maximalAbelianExtension p U) : Normal (localField p U) M := by
  haveI : IsGalois (localField p U) (AlgebraicClosure ℚ_[p]) := inferInstance
  haveI h : M.fixingSubgroup.Normal :=
    fixingSubgroup_normal_of_le_maximalAbelianExtension p U M hM
  exact (InfiniteGalois.normal_iff_isGalois M).mp h |>.to_normal

end LeanFormal.IUT.XiFPaper.S2047GeneralLocalCFTActual
