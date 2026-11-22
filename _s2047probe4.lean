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

-- P1: integrality of elements of L^ab
example (y : ↥(maximalAbelianExtension p U)) :
    IsIntegral (localField p U) (y : AlgebraicClosure ℚ_[p]) := by
  haveI : Algebra.IsAlgebraic (localField p U) (AlgebraicClosure ℚ_[p]) := inferInstance
  exact (Algebra.IsAlgebraic.isAlgebraic (R := localField p U) (A := AlgebraicClosure ℚ_[p]) (x := (y : AlgebraicClosure ℚ_[p]))).isIntegral

-- P2: adjoin finite
example (y : ↥(maximalAbelianExtension p U)) :
    FiniteDimensional (localField p U)
      (IntermediateField.adjoin (localField p U) {(y : AlgebraicClosure ℚ_[p])}) := by
  apply IntermediateField.adjoin.finiteDimensional
  haveI : Algebra.IsAlgebraic (localField p U) (AlgebraicClosure ℚ_[p]) := inferInstance
  exact (Algebra.IsAlgebraic.isAlgebraic (R := localField p U) (A := AlgebraicClosure ℚ_[p]) (x := (y : AlgebraicClosure ℚ_[p]))).isIntegral

-- P3: adjoin ≤ L^ab
example (y : ↥(maximalAbelianExtension p U)) :
    IntermediateField.adjoin (localField p U) {(y : AlgebraicClosure ℚ_[p])} ≤
      maximalAbelianExtension p U := by
  rw [IntermediateField.adjoin_le_iff]
  rintro z rfl
  exact y.2

end LeanFormal.IUT.XiFPaper.S2047GeneralLocalCFTActual
