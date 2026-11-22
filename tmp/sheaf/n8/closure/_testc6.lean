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

-- Try to obtain the topological/measure instances for the tensor block.
example : ProperSpace (ArithmeticTensorTupleBlock places tuple) := by
  infer_instance

example : LocallyCompactSpace (ArithmeticTensorTupleBlock places tuple) := by
  infer_instance

example : MeasurableSpace (ArithmeticTensorTupleBlock places tuple) := by
  infer_instance

example : BorelSpace (ArithmeticTensorTupleBlock places tuple) := by
  infer_instance

example : Nonempty (C6ActualIQData places tuple) := by
  letI : MeasurableSpace (ArithmeticTensorTupleBlock places tuple) := borel _
  letI : BorelSpace (ArithmeticTensorTupleBlock places tuple) := ⟨rfl⟩
  letI : ProperSpace (ArithmeticTensorTupleBlock places tuple) := inferInstance
  letI : LocallyCompactSpace (ArithmeticTensorTupleBlock places tuple) := locallyCompact_of_proper
  let mu := Measure.addHaar (ArithmeticTensorTupleBlock places tuple)
  letI : Measure.IsAddHaarMeasure mu := inferInstance
  exact ⟨C6ActualIQData.actual places tuple mu⟩

end
