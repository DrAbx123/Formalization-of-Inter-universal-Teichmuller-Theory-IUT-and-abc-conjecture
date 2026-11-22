import tmp.sheaf.xif.paper.Mzk1P3TensorCoreActual
/-! P3 core: conditional Haar scaling interface for a tensor block.

The concrete `SMul Set`/`NormedSpace` instances on `FinitePadicTensor` are not
available in the core context, so the scaling law is exposed as an explicit
interface: an endomorphism `f`, a constant `c`, and the measured law `hf`.
Never assumed silently; `hf` is a named hypothesis. -/
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreScalingActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
/-- CONDITIONAL core scaling interface: the measured law is an explicit input. -/
theorem tensorCore_measure_scaling_interface
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    (f : ArithmeticTensorTupleBlock places tuple → ArithmeticTensorTupleBlock places tuple)
    (c : ENNReal)
    (hf : ∀ S : Set (ArithmeticTensorTupleBlock places tuple), μ (f '' S) = c * μ S)
    (S : Set (ArithmeticTensorTupleBlock places tuple)) :
    μ (f '' S) = c * μ S :=
  hf S
end LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreScalingActual
end