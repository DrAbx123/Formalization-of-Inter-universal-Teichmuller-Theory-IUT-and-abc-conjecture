import LeanFormal.IUT.IUTI.HodgeTheater.SourceThetaLinkGraphAutomorphismReduction

/-! Mainline: Frobenius-picture graph automorphisms form a subgroup (real proof). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FrobeniusGraphAutSubgroupActual

open LeanFormal.IUT

/-- Subgroup of graph automorphisms of the Frobenius-picture Gamma. -/
def FrobeniusPictureAutSubgroup : Subgroup (Equiv.Perm ℤ) where
  carrier := {σ | FrobeniusPictureGraphAut σ}
  one_mem' := graphAut_one
  mul_mem' := by
    intro a b ha hb
    exact graphAut_mul hb ha
  inv_mem' := by
    intro a ha
    exact graphAut_symm ha

theorem mem_frobeniusAutSubgroup_iff (σ : Equiv.Perm ℤ) :
    σ ∈ FrobeniusPictureAutSubgroup ↔ FrobeniusPictureGraphAut σ :=
  Iff.rfl

theorem frobeniusAutSubgroup_eq_translations (σ : Equiv.Perm ℤ) :
    σ ∈ FrobeniusPictureAutSubgroup ↔ ∃ k : ℤ, σ = chainTranslation k :=
  graphAut_translation σ

end LeanFormal.IUT.XiFPaper.Mzk1FrobeniusGraphAutSubgroupActual