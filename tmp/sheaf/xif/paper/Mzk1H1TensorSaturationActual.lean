import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQTensor

noncomputable section
universe u v w
namespace LeanFormal.IUT.XiFPaper.Mzk1H1TensorSaturationActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)

structure H1TensorSaturationData where
  region : Set (ArithmeticPacketTensor places)
  isCompact : IsCompact region
  one_mem : (1 : ArithmeticPacketTensor places) ∈ region

def h1TensorSaturationActual : H1TensorSaturationData places :=
  { region := arithmeticTensorLogRegion places
    isCompact := isCompact_arithmeticTensorLogRegion places
    one_mem := one_mem_arithmeticTensorLogRegion places }

end LeanFormal.IUT.XiFPaper.Mzk1H1TensorSaturationActual
end
