import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQTensor
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
#synth MeasurableSpace (ArithmeticPacketTensor places)
#synth NormedAddCommGroup (ArithmeticPacketTensor places)
#synth Measure.IsAddHaarMeasure (Measure.addHaar : Measure (ArithmeticPacketTensor places))
end
