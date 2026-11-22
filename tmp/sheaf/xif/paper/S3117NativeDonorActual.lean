import tmp.sheaf.xif.paper.S3117RootCarrierAudit
import tmp.sheaf.xif.paper.S3115NativeSourcePilotRegionDonors

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.S3117RootCarrierAudit
open LeanFormal.IUT.XiFPaper.S3115NativeSourcePilotRegionDonors
open LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource
open LeanFormal.IUT.XiFPaper.S3094ActualQFamilyAttempt
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.S3117NativeDonorActual

variable (X : N8NativeInput fiveLabel)
variable [Fintype (Bad (nativePlaceSelection X.S))]

/-- Corrected native donor with algebraic-closure root carrier. -/
structure S3117NativeSourcePilotRegionDonors where
  place : FinitePlaceAtPrime X.S.arithmetic.Fmod (nativeC3Prime X)
  q : FinitePlaceQCandidate (nativeFPlaceOverBad X)
  thetaPacket : FiniteThetaPacket fiveLabel
  qUnit : (Completion (nativeFPlaceOverBad X))ˣ
  roots : NatRootSystem (unitToAlgClosed qUnit)
  roots' : NatRootSystem (unitToAlgClosed qUnit)
  kummerClass : CyclotomicTower
    (AlgebraicClosure (Completion (nativeFPlaceOverBad X)))
  rootChange : CyclotomicTower
    (AlgebraicClosure (Completion (nativeFPlaceOverBad X)))
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'
  tensorPrime : Nat
  [tensorPrimeFact : Fact tensorPrime.Prime]
  tensorIndex : Type
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex -> Type
  tensorPlaces : (i : tensorIndex) -> tensorPlaceIndex i ->
    FinitePlaceAtPrime X.S.arithmetic.Fmod tensorPrime
  tensorTuple : (i : tensorIndex) -> tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ
  tensorLanding : Completion (nativeFPlaceOverBad X) ->
    ArithmeticTensorTupleBlock tensorPlaces tensorTuple
  tensorLanding_q : tensorLanding (q.q : Completion (nativeFPlaceOverBad X)) =
    (tensorUnit : ArithmeticTensorTupleBlock tensorPlaces tensorTuple)

attribute [instance] S3117NativeSourcePilotRegionDonors.tensorPrimeFact
attribute [instance] S3117NativeSourcePilotRegionDonors.tensorFintype

/-- Actual conditional donor: native place/q/theta, corrected BK, explicit BT. -/
noncomputable def S3117NativeDonor
    (BK : S3117BK X) (BT : S3115BT X) :
    S3117NativeSourcePilotRegionDonors X where
  place := nativeC3Place X
  q := nativeQActual X
  thetaPacket := S3094Packet (T := X.S)
  qUnit := BK.qUnit
  roots := BK.roots
  roots' := BK.roots'
  kummerClass := BK.kummerClass
  rootChange := BK.rootChange
  rootChange_eq := BK.rootChange_eq
  tensorPrime := BT.p
  tensorPrimeFact := BT.hp
  tensorIndex := BT.tensorIndex
  tensorFintype := BT.tensorFintype
  tensorPlaceIndex := BT.tensorPlaceIndex
  tensorPlaces := BT.tensorPlaces
  tensorTuple := BT.tensorTuple
  tensorUnit := BT.tensorUnit
  tensorLanding := BT.tensorLanding
  tensorLanding_q := BT.tensorLanding_q

#check S3117NativeSourcePilotRegionDonors
#check S3117NativeDonor

end LeanFormal.IUT.XiFPaper.S3117NativeDonorActual
end