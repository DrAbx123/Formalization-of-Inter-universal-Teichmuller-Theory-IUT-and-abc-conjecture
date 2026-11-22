import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks

noncomputable section
universe u v w
namespace LeanFormal.IUT.XiFPaper.Mzk1H1CoordinateMinimumActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)

structure H1CoordinateMinimumData where
  decomposition : ArithmeticPacketTensor places ≃+*
    ((tuple : (i : ι) → V i) → ArithmeticTensorTupleBlock places tuple)

def h1CoordinateMinimumActual : H1CoordinateMinimumData places :=
  { decomposition := (arithmeticTensorBlocksAlgEquiv places).toRingEquiv }

end LeanFormal.IUT.XiFPaper.Mzk1H1CoordinateMinimumActual
end
