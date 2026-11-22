import tmp.sheaf.xif.paper.Mzk1P3NativeDReanchorActual
/-! #6/#1: cardinality obstruction for `BlockProductAlignmentData`.
The tensor-core factor type `J` has cardinal at most the block dimension,
while an alignment `J ≃ Bad` needs `card Bad`; if `card Bad` exceeds the block
dimension, no alignment exists. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P3BlockProductAlignmentObstructionActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1TensorCoreWitnessActual
open LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1P3NativeDReanchorActual
variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
/-- The number of field factors in any tensor-core witness is at most the
block dimension. -/
theorem card_witness_le_finrank (tuple : (i : ι) → V i)
    (W : TensorCoreWitness places tuple) [Fintype W.J] :
    Fintype.card W.J ≤ Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) := by
  letI : ∀ j, NontriviallyNormedField (W.E j) := W.field
  letI : ∀ j, NormedAlgebra ℚ_[p] (W.E j) := W.alg
  letI : ∀ j, FiniteDimensional ℚ_[p] (W.E j) := W.finite
  have hsum := tensorCore_finrank_eq_sum places tuple W.E W.equiv
  rw [hsum]
  calc Fintype.card W.J = ∑ _j : W.J, 1 := by simp
    _ ≤ ∑ j : W.J, Module.finrank ℚ_[p] (W.E j) := by
        apply Finset.sum_le_sum
        intro j _
        have hpos : 0 < Module.finrank ℚ_[p] (W.E j) := by
          rw [Module.finrank_pos_iff_of_free]
          infer_instance
        omega
/-- If `card Bad` exceeds the block dimension, no tensor-core witness admits an
equivalence `J ≃ Bad`. -/
theorem no_witness_jEquiv_of_card_gt
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))]
    (tuple : (i : ι) → V i) (W : TensorCoreWitness places tuple) [Fintype W.J]
    (h : Fintype.card (Bad (nativePlaceSelection T)) >
      Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple)) :
    ¬ Nonempty (W.J ≃ Bad (nativePlaceSelection T)) := by
  rintro ⟨e⟩
  have hle := card_witness_le_finrank places tuple W
  have hcard : Fintype.card W.J = Fintype.card (Bad (nativePlaceSelection T)) :=
    Fintype.card_congr e
  omega
end LeanFormal.IUT.XiFPaper.Mzk1P3BlockProductAlignmentObstructionActual
end