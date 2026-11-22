import tmp.sheaf.xif.paper.S2027LocalArtinActual
import Reciprocity.Artin
noncomputable section
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.S2056MaxAbelianBridge
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
variable {p : Nat} [Fact (Nat.Prime p)]
variable (U : LeanFormal.IUT.XiFPaper.S2017VerlagerungActual.Index p)
/-- LANA's maxAbelian is contained in S2027's maximalAbelianExtension. -/
theorem maxAbelian_le_maximalAbelianExtension :
    PadicField.maxAbelian (localField p U) (AlgebraicClosure ℚ_[p]) ≤ maximalAbelianExtension p U := by
  rw [PadicField.maxAbelian]
  apply iSup_le
  intro L
  exact le_maximalAbelianExtension_of_isAbelianGalois p U L.1
/-- Exact missing reverse equality. -/
def MaxAbelianEquality : Prop :=
  PadicField.maxAbelian (localField p U) (AlgebraicClosure ℚ_[p]) = maximalAbelianExtension p U
/-- Exact missing finite-subextension lemma: every element of L^ab lies in a
finite abelian subextension (then LANA maxAbelian contains it). -/
def FiniteAbelianSubextension : Prop :=
  ∀ x : maximalAbelianExtension p U, ∃ (L : PadicField.AbFin (localField p U) (AlgebraicClosure ℚ_[p])),
    (x : AlgebraicClosure ℚ_[p]) ∈ L.1
end LeanFormal.IUT.XiFPaper.S2056MaxAbelianBridge
end
#print axioms LeanFormal.IUT.XiFPaper.S2056MaxAbelianBridge.maxAbelian_le_maximalAbelianExtension
