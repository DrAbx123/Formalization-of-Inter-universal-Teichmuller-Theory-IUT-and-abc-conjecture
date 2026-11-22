import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlockFields
import tmp.sheaf.xif.paper.Mzk1C3BlockMeasureActual
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.Pi

/-! P7 #7 route B2: field-product decomposition => dimension product=sum,
and the C3 block degree as the sum of actual local degrees. -/
noncomputable section
open scoped BigOperators
set_option linter.overlappingInstances false
namespace LeanFormal.IUT.XiFPaper.Mzk1P7ThetaDegB2Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.Mzk1C3BlockMeasureActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion

variable {K : Type*} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)

/-- B2: a field-product decomposition turns the block dimension into a sum. -/
theorem finrank_arithmeticTensorTupleBlock_eq_sum_fieldProduct
    (tuple : (i : ι) → V i) {J : Type*} [Fintype J] (E : J → Type*)
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)]
    [∀ j, Module.Free ℚ_[p] (E j)] [∀ j, Module.Finite ℚ_[p] (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) =
      ∑ j, Module.finrank ℚ_[p] (E j) := by
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]

/-- Packet tensor dimension as sum over tuple blocks and field components. -/
theorem finrank_arithmeticPacketTensor_eq_sum_fieldProduct
    {J : ((i : ι) → V i) → Type*} [∀ tuple, Fintype (J tuple)]
    (E : (tuple : (i : ι) → V i) → J tuple → Type*)
    [∀ tuple j, NormedField (E tuple j)]
    [∀ tuple j, NormedAlgebra ℚ_[p] (E tuple j)]
    [∀ tuple j, FiniteDimensional ℚ_[p] (E tuple j)]
    [∀ tuple j, Module.Free ℚ_[p] (E tuple j)]
    [∀ tuple j, Module.Finite ℚ_[p] (E tuple j)]
    (e : ∀ tuple, ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]]
      ((j : J tuple) → E tuple j)) :
    Module.finrank ℚ_[p] (ArithmeticPacketTensor places) =
      ∑ tuple, ∑ j, Module.finrank ℚ_[p] (E tuple j) := by
  have hblocks : Module.finrank ℚ_[p] (ArithmeticPacketTensor places) =
      ∑ tuple, Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) :=
    (arithmeticTensorBlocksAlgEquiv places).toLinearEquiv.finrank_eq.trans
      (Module.finrank_pi_fintype ℚ_[p])
  calc
    Module.finrank ℚ_[p] (ArithmeticPacketTensor places)
        = ∑ tuple, Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) := hblocks
    _ = ∑ tuple, ∑ j, Module.finrank ℚ_[p] (E tuple j) := by
          apply Finset.sum_congr rfl
          intro tuple _
          exact finrank_arithmeticTensorTupleBlock_eq_sum_fieldProduct places tuple (E tuple) (e tuple)


end LeanFormal.IUT.XiFPaper.Mzk1P7ThetaDegB2Actual
end