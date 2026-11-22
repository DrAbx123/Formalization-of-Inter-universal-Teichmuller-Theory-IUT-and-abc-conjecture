import tmp.sheaf.xif.paper.Mzk1P3TensorCoreActual
/-! P3 core: normalized log-volume on a tensor block (no C3). -/
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreNormalizedActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
noncomputable def tensorBlockNormalizedLogVolume
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    (S : Set (ArithmeticTensorTupleBlock places tuple)) : ℝ :=
  Real.log (μ S).toReal /
    (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ)
end LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreNormalizedActual
end