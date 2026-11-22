import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQTensor
import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion
variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0,0,0,0,0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]
abbrev LiteralIQIndex (j : Nat) : Type := Fin (j+1) × C3.tensorIndex
abbrev LiteralIQPlaceIndex (j : Nat) : LiteralIQIndex C3 j -> Type := fun x => C3.tensorPlaceIndex x.2
def literalIQPlaces (j : Nat) : (x : LiteralIQIndex C3 j) -> LiteralIQPlaceIndex C3 j x -> FinitePlaceAtPrime I.initial.arithmetic.Fmod C3.p := fun x => C3.tensorPlaces x.2
abbrev LiteralIQAmbient (j : Nat) : Type := ArithmeticPacketTensor (literalIQPlaces C3 j)
#check LiteralIQIndex
#check LiteralIQPlaceIndex
#check literalIQPlaces
#check LiteralIQAmbient
end