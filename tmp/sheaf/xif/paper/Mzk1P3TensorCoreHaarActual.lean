import tmp.sheaf.xif.paper.Mzk1P3TensorCoreActual
/-! P3 core: per-block Haar positivity and compact-region finiteness (no C3). -/
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreHaarActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
theorem tensorBlockHaar_pos
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    {U : Set (ArithmeticTensorTupleBlock places tuple)}
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U :=
  hU.measure_pos μ hne
theorem tensorBlockHaar_lt_top
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ]
    {Kset : Set (ArithmeticTensorTupleBlock places tuple)}
    (hK : IsCompact Kset) : μ Kset < ⊤ :=
  hK.measure_lt_top
end LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreHaarActual
end