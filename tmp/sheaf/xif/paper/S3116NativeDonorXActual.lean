import tmp.sheaf.xif.paper.C3DonorFieldsFromSource

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.S3116NativeDonorXActual

variable {l : PrimeGeFive} (X : N8NativeInput l)

structure NativeC3DonorX where
  pF : Nat
  [hpF : Fact pF.Prime]
  placeF : FinitePlaceAtPrime X.S.arithmetic.F pF
  q : FinitePlaceQCandidate placeF.val
  thetaPacket : FiniteThetaPacket l
  roots : NatRootSystem (candidateUnits placeF q)
  roots' : NatRootSystem (candidateUnits placeF q)
  kummerClass : CyclotomicTower (CommonPrimeCompletion placeF)
  rootChange : CyclotomicTower (CommonPrimeCompletion placeF)
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'
  pBase : Nat
  [hpBase : Fact pBase.Prime]
  basePlace : FinitePlaceAtPrime X.S.arithmetic.Fmod pBase
  tensorIndex : Type
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex -> Type
  tensorPlaces : (i : tensorIndex) -> tensorPlaceIndex i ->
    FinitePlaceAtPrime X.S.arithmetic.Fmod pBase
  tensorTuple : (i : tensorIndex) -> tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ
  tensorLanding : CommonPrimeCompletion placeF ->
    ArithmeticTensorTupleBlock tensorPlaces tensorTuple
  tensorLanding_q : tensorLanding (q.q : CommonPrimeCompletion placeF) =
    (tensorUnit : ArithmeticTensorTupleBlock tensorPlaces tensorTuple)

abbrev nativeFPrime : Nat :=
  (completionRationalPrime (nativeFPlaceOverBad X)).val

instance nativeFPrimeFact : Fact (Nat.Prime (nativeFPrime X)) :=
  ⟨(completionRationalPrime (nativeFPlaceOverBad X)).2⟩

def nativeFPlaceAtPrime :
    FinitePlaceAtPrime X.S.arithmetic.F (nativeFPrime X) :=
  ⟨nativeFPlaceOverBad X, rfl⟩

structure NativeRootKummerData
    (place : FinitePlaceAtPrime X.S.arithmetic.F (nativeFPrime X))
    (q : FinitePlaceQCandidate place.val) where
  roots : NatRootSystem (candidateUnits place q)
  roots' : NatRootSystem (candidateUnits place q)
  kummerClass : CyclotomicTower (CommonPrimeCompletion place)
  rootChange : CyclotomicTower (CommonPrimeCompletion place)
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'


/-- Tensor data over a chosen native F-place, with a base Fmod place. -/
structure NativeTensorDataF
    (placeF : FinitePlaceAtPrime X.S.arithmetic.F (nativeFPrime X)) where
  pBase : Nat
  [hpBase : Fact pBase.Prime]
  basePlace : FinitePlaceAtPrime X.S.arithmetic.Fmod pBase
  tensorIndex : Type
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex -> Type
  tensorPlaces : (i : tensorIndex) -> tensorPlaceIndex i ->
    FinitePlaceAtPrime X.S.arithmetic.Fmod pBase
  tensorTuple : (i : tensorIndex) -> tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ
  tensorLanding : CommonPrimeCompletion placeF ->
    ArithmeticTensorTupleBlock tensorPlaces tensorTuple

def NativeC3DonorXTarget : Prop :=
  Nonempty (NativeC3DonorX X)

#check NativeC3DonorX
#check nativeFPrime
#check nativeFPlaceAtPrime
#check NativeRootKummerData
#check NativeC3DonorXTarget

end LeanFormal.IUT.XiFPaper.S3116NativeDonorXActual
end
