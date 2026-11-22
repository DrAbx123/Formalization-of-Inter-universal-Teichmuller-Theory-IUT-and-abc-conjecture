import tmp.sheaf.xif.paper.S2027LocalArtinActual
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.FieldTheory.Galois.Infinite

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

#check @IntermediateField.subset_adjoin
#check @IntermediateField.finiteDimensional_adjoin
#check @QuotientGroup.lift
#check @QuotientGroup.mk
#check @QuotientGroup.ker_mk'
#check @AlgEquiv.restrictNormalHom_apply

example (y z : AlgebraicClosure ℚ_[p]) : Finite ({y, z} : Set (AlgebraicClosure ℚ_[p])) := inferInstance

end LeanFormal.IUT.XiFPaper.S2047GeneralLocalCFTActual
