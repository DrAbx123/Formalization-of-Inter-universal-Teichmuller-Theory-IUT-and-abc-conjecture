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

variable (p : Nat) [Fact (Nat.Prime p)]

example (U : Index p) (M N : IntermediateField (localField p U) (AlgebraicClosure ℚ_[p]))
    (h : M ≤ N) : Algebra M N := inferInstance

example (U : Index p) (M : IntermediateField (localField p U) (AlgebraicClosure ℚ_[p]))
    [FiniteDimensional (localField p U) M] : (Mˣ →* (localField p U)ˣ) :=
  Units.map (Algebra.norm (localField p U))

end LeanFormal.IUT.XiFPaper.S2047GeneralLocalCFTActual
