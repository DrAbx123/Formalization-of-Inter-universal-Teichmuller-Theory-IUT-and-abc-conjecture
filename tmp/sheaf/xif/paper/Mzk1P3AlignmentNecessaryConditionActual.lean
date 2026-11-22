import tmp.sheaf.xif.paper.Mzk1P3BlockProductAlignmentObstructionActual
import tmp.sheaf.xif.paper.Mzk1P3NativeDReanchorActual
/-! #6: necessary cardinality condition for `BlockProductAlignmentData`. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3AlignmentNecessaryConditionActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1TensorCoreWitnessActual
open LeanFormal.IUT.XiFPaper.Mzk1P3NativeDReanchorActual
open LeanFormal.IUT.XiFPaper.Mzk1P3BlockProductAlignmentObstructionActual
variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
/-- An alignment forces `card Bad` to be the number of tensor-core factors. -/
theorem card_bad_eq_card_witness_of_alignment
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))]
    (tuple : (i : ι) → V i)
    (D : BlockProductAlignmentData T places tuple) :
    Fintype.card (Bad (nativePlaceSelection T)) =
      @Fintype.card ((tensorCoreWitness places tuple).J) (tensorCoreWitness places tuple).fintype := by
  letI : Fintype (tensorCoreWitness places tuple).J :=
    (tensorCoreWitness places tuple).fintype
  exact (Fintype.card_congr D.JEquiv).symm
/-- Necessary cardinality condition: an alignment implies `card Bad` is at most
the tensor-block dimension. -/
theorem card_bad_le_finrank_of_alignment
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))]
    (tuple : (i : ι) → V i)
    (D : BlockProductAlignmentData T places tuple) :
    Fintype.card (Bad (nativePlaceSelection T)) ≤
      Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) := by
  letI : Fintype (tensorCoreWitness places tuple).J :=
    (tensorCoreWitness places tuple).fintype
  have hcard := card_bad_eq_card_witness_of_alignment (places := places) (T := T) (tuple := tuple) D
  have hle := card_witness_le_finrank places tuple (tensorCoreWitness places tuple)
  omega
/-- Consequently, if `card Bad` exceeds the block dimension, no alignment data
exists. -/
theorem no_alignment_of_card_gt
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))]
    (tuple : (i : ι) → V i)
    (h : Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) <
      Fintype.card (Bad (nativePlaceSelection T))) :
    ¬ Nonempty (BlockProductAlignmentData T places tuple) := by
  rintro ⟨D⟩
  have hle := card_bad_le_finrank_of_alignment (places := places) (T := T) (tuple := tuple) D
  omega
end LeanFormal.IUT.XiFPaper.Mzk1P3AlignmentNecessaryConditionActual
end