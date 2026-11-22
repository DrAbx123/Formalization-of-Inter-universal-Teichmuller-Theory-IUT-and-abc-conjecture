import tmp.sheaf.xif.paper.Mzk1H1TensorSaturationActual

noncomputable section
universe u v w
namespace LeanFormal.IUT.XiFPaper.Mzk1H1LowerBoundActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1H1TensorSaturationActual
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)

structure H1LowerBoundData where
  saturation : H1TensorSaturationData places
  one_mem : (1 : ArithmeticPacketTensor places) ∈ saturation.region

def h1LowerBoundActual : H1LowerBoundData places :=
  { saturation := h1TensorSaturationActual places
    one_mem := one_mem_arithmeticTensorLogRegion places }

theorem h1LowerBound_witness :
    ∃ x : ArithmeticPacketTensor places, x ∈ (h1LowerBoundActual places).saturation.region :=
  ⟨1, (h1LowerBoundActual places).one_mem⟩

end LeanFormal.IUT.XiFPaper.Mzk1H1LowerBoundActual
end
