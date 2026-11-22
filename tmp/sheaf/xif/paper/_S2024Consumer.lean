import tmp.sheaf.xif.paper.S2024LocalReciprocityActual

noncomputable section
open scoped DirectSum
open LeanFormal.IUT
open LeanFormal.IUT.LocalMLFModelTMPair
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2011Cor110bActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2024LocalReciprocityActual

namespace LeanFormal.IUT.XiFPaper.S2024Consumer

variable (p : Nat) [Fact (Nat.Prime p)]

-- The formal (M2) datum and the missing propositions are statable types/props.
example : Type := LocalReciprocityData p
example : Prop := localReciprocityDataMissing p
example : Prop := localReciprocityLevelwiseMissing p
example : Prop := localReciprocityOnTorsionMissing p
example (U : Index p) : Prop := levelwiseLocalReciprocity p U

-- The reduction theorems.
example (data : LocalReciprocityData p) : localReciprocityOnTorsion p :=
  localReciprocityOnTorsion_of_data p data
example (data : LocalReciprocityData p) : muQZComparison p :=
  muQZComparison_of_data p data
example (data : LocalReciprocityData p) : muHatComparison p :=
  muHatComparison_of_data p data
example (data : LocalReciprocityData p) : Nonempty (muQZ p ≃+ AddCircle (1 : ℚ)) :=
  muQZ_addEquiv_addCircle_of_data p data
example (data : LocalReciprocityData p) {H K : Index p} (h : H ≤ K) :
    Function.Injective (toStage p h) :=
  toStage_injective_of_data p data h

-- The single-stage representation is unconditional.
example (x : muQZ p) : ∃ (L : Index p) (w : Stage p L), x = muQZof p L w :=
  muQZ_exists_stage p x

#print axioms muQZComparison_of_data
#print axioms muHatComparison_of_data
#print axioms muQZ_exists_stage

end LeanFormal.IUT.XiFPaper.S2024Consumer
