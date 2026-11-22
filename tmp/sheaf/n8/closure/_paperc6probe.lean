import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQHull

set_option maxHeartbeats 800000

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8C6ActualIQ
open MeasureTheory
open LeanFormal.IUT.LocalFieldPadicTensor
open scoped BigOperators

namespace Probe
variable {l : PrimeGeFive} (S : SourceInitialThetaData l)
def p0 : NumberField.FinitePlace S.candidate.arithmetic.Fmod := Classical.choose S.clauseB.bad_nonempty
def p (S : SourceInitialThetaData l) : Nat := (completionRationalPrime (p0 S)).val
instance factP (S : SourceInitialThetaData l) : Fact (p S).Prime := ⟨(completionRationalPrime (p0 S)).property⟩
abbrev Idx (S : SourceInitialThetaData l) := FinitePlaceAtPrime S.candidate.arithmetic.Fmod (p S)
instance (S : SourceInitialThetaData l) : Fintype (Idx S) := fintype_fullPrimePlaces
def places : (i : Idx S) → PUnit → FinitePlaceAtPrime S.candidate.arithmetic.Fmod (p S) := fun i _ => i
def tuple : (i : Idx S) → PUnit := fun _ => PUnit.unit
local instance : MeasurableSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) := borel _
local instance : BorelSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) := ⟨rfl⟩
local instance : ProperSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) :=
  FiniteDimensional.proper ℚ_[p S] (ArithmeticTensorTupleBlock (places S) (tuple S))
#check ArithmeticTensorTupleBlock (places S) (tuple S)
#check (Measure.addHaar : Measure (ArithmeticTensorTupleBlock (places S) (tuple S)))
def B : C6ActualIQData (places S) (tuple S) (Measure.addHaar) := C6ActualIQData.actual (places S) (tuple S) (Measure.addHaar)
end Probe

end