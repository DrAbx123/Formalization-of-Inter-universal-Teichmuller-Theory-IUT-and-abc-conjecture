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

#check @IntermediateField.fixingSubgroup
#check @IntermediateField.fixingSubgroup_antitone
#check @IntermediateField.le_iff_le
#check @Subgroup.commutator_top_left_le_iff
#check @Subgroup.commutator_mono
#check @Subgroup.le_topologicalClosure
#check @Subgroup.topologicalClosure_minimal
#check @IsGalois.to_normal

end LeanFormal.IUT.XiFPaper.S2047GeneralLocalCFTActual
