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

example : True := by
  letI : MeasurableSpace (ArithmeticTensorTupleBlock places tuple) :=
    borel (ArithmeticTensorTupleBlock places tuple)
  letI : BorelSpace (ArithmeticTensorTupleBlock places tuple) := ⟨rfl⟩
  letI : LocallyCompactSpace (ArithmeticTensorTupleBlock places tuple) := locallyCompact_of_proper
  let mu : Measure (ArithmeticTensorTupleBlock places tuple) := MeasureTheory.Measure.addHaar
  letI : Measure.IsAddHaarMeasure mu := inferInstance
  have h : Nonempty (C6ActualIQData places tuple) := ⟨C6ActualIQData.actual places tuple mu⟩
  trivial

end
