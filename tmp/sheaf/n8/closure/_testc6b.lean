import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8C6ActualIQ
open MeasureTheory

noncomputable section

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {V : iota -> Type} [∀ i, Fintype (V i)]
variable (places : (i : iota) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> V i)

abbrev Block := ArithmeticTensorTupleBlock places tuple

example : TopologicalSpace Block := inferInstance
example : ProperSpace Block := inferInstance
example : MeasurableSpace Block := borel Block
example : BorelSpace Block := ⟨rfl⟩

example : Nonempty (C6ActualIQData places tuple) := by
  letI : MeasurableSpace Block := borel Block
  letI : BorelSpace Block := ⟨rfl⟩
  letI : LocallyCompactSpace Block := locallyCompact_of_proper
  let mu : Measure Block := MeasureTheory.Measure.addHaar
  letI : Measure.IsAddHaarMeasure mu := inferInstance
  exact ⟨C6ActualIQData.actual places tuple mu⟩

end
