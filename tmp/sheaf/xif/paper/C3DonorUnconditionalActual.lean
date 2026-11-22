import tmp.sheaf.xif.paper.BasePlaceQCandidateActual
import tmp.sheaf.xif.paper.C3DonorFieldsFromSource
import tmp.sheaf.n8.closure.C3Actual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.C3DonorUnconditionalActual

variable {l : PrimeGeFive} (X : N8NativeInput l)

structure BaseRootKummerData
    (q : FinitePlaceQCandidate (nativeC3Place X).val) where
  roots : NatRootSystem (candidateUnits (nativeC3Place X) q)
  roots' : NatRootSystem (candidateUnits (nativeC3Place X) q)
  kummerClass : CyclotomicTower (CommonPrimeCompletion (nativeC3Place X))
  rootChange : CyclotomicTower (CommonPrimeCompletion (nativeC3Place X))
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'

structure BaseTensorData
    (q : FinitePlaceQCandidate (nativeC3Place X).val) where
  tensorIndex : Type
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex -> Type
  tensorPlaces : (i : tensorIndex) -> tensorPlaceIndex i ->
    FinitePlaceAtPrime X.S.arithmetic.Fmod (nativeC3Prime X)
  tensorTuple : (i : tensorIndex) -> tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ
  tensorLanding :
    CommonPrimeCompletion (nativeC3Place X) ->
      ArithmeticTensorTupleBlock tensorPlaces tensorTuple
  tensorLanding_q : tensorLanding
      (q.q : CommonPrimeCompletion (nativeC3Place X)) =
    (tensorUnit : ArithmeticTensorTupleBlock tensorPlaces tensorTuple)

end LeanFormal.IUT.XiFPaper.C3DonorUnconditionalActual
end
