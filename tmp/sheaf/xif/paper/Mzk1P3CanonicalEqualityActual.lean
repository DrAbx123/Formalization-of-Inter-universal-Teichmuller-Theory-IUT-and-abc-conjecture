import tmp.sheaf.xif.paper.Mzk1P3CanonicalEqualityObstructionActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
/-! #6/#1 actual qVFam equality case: a canonical alignment of the actual
one-factor qVFam tensor block with the full root-extension product forces a
concrete dimension equation, and the equality case forces all root-extension
degrees to be 1. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P3CanonicalEqualityActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1P3CanonicalEqualityObstructionActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- A canonical alignment of the actual qVFam block with the full root product
forces the dimension equation `finrank block = Σ_b finrank rootExtension_b`. -/
theorem qVFam_canonical_finrank_eq
    [∀ b', Algebra ℚ_[qVFamTensorP T b] (rootNormedExtension T b')]
    [∀ b', FiniteDimensional ℚ_[qVFamTensorP T b] (rootNormedExtension T b')]
    (e : ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple ≃ₐ[ℚ_[qVFamTensorP T b]]
      ((b' : Bad (nativePlaceSelection T)) → rootNormedExtension T b')) :
    Module.finrank ℚ_[qVFamTensorP T b]
        (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple) =
      ∑ b' : Bad (nativePlaceSelection T),
        Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b') := by
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
/-- Degree obstruction in the actual qVFam equality case: one root-extension
factor of degree > 1 forces `card Bad < finrank block`. -/
theorem qVFam_canonical_card_lt_finrank
    [∀ b', Algebra ℚ_[qVFamTensorP T b] (rootNormedExtension T b')]
    [∀ b', FiniteDimensional ℚ_[qVFamTensorP T b] (rootNormedExtension T b')]
    (e : ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple ≃ₐ[ℚ_[qVFamTensorP T b]]
      ((b' : Bad (nativePlaceSelection T)) → rootNormedExtension T b'))
    (b0 : Bad (nativePlaceSelection T))
    (h0 : 1 < Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b0)) :
    Fintype.card (Bad (nativePlaceSelection T)) <
      Module.finrank ℚ_[qVFamTensorP T b]
        (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple) := by
  have h := canonical_card_lt_finrank (T := T)
    (K := T.arithmetic.F) (p := qVFamTensorP T b)
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple) e b0 h0
  simpa using h
/-- Equality case for the actual qVFam block: if the cardinal equals the block
dimension, every root-extension factor has degree 1. -/
theorem qVFam_canonical_all_degree_one_of_card_eq_finrank
    [∀ b', Algebra ℚ_[qVFamTensorP T b] (rootNormedExtension T b')]
    [∀ b', FiniteDimensional ℚ_[qVFamTensorP T b] (rootNormedExtension T b')]
    (e : ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple ≃ₐ[ℚ_[qVFamTensorP T b]]
      ((b' : Bad (nativePlaceSelection T)) → rootNormedExtension T b'))
    (h : Fintype.card (Bad (nativePlaceSelection T)) =
      Module.finrank ℚ_[qVFamTensorP T b]
        (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple)) :
    ∀ b', Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b') = 1 := by
  exact canonical_all_degree_one_of_card_eq_finrank (T := T)
    (K := T.arithmetic.F) (p := qVFamTensorP T b)
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple) e h
end LeanFormal.IUT.XiFPaper.Mzk1P3CanonicalEqualityActual
end