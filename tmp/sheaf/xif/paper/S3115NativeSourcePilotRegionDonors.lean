import tmp.sheaf.n8.closure.C3Actual
import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.xif.paper.C3DonorFieldsFromSource
import tmp.sheaf.xif.paper.S3094ActualQFamilyAttempt
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource
open LeanFormal.IUT.XiFPaper.S3094ActualQFamilyAttempt
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3115NativeSourcePilotRegionDonors

variable (X : N8NativeInput fiveLabel)
variable [Fintype (Bad (nativePlaceSelection X.S))]


/-- The candidate unit at the native F completion, from a q-candidate. -/
noncomputable def S3115CandidateUnits
    (q : FinitePlaceQCandidate (nativeFPlaceOverBad X)) :
    (Completion (nativeFPlaceOverBad X))ˣ :=
  Units.mk0 q.q q.q_ne_zero


/-- Base q/root/Kummer data at the native F-place. -/
structure S3115BK where
  qUnit : (Completion (nativeFPlaceOverBad X))ˣ
  qUnit_eq : qUnit = S3115CandidateUnits X (nativeQActual X)
  roots : NatRootSystem qUnit
  roots' : NatRootSystem qUnit
  kummerClass : CyclotomicTower (Completion (nativeFPlaceOverBad X))
  rootChange : CyclotomicTower (Completion (nativeFPlaceOverBad X))
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'

/-- Base tensor landing data at the native F completion. -/
structure S3115BT where
  p : Nat
  [hp : Fact p.Prime]
  tensorIndex : Type
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex -> Type
  tensorPlaces : (i : tensorIndex) -> tensorPlaceIndex i ->
    FinitePlaceAtPrime X.S.arithmetic.Fmod p
  tensorTuple : (i : tensorIndex) -> tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ
  tensorLanding : Completion (nativeFPlaceOverBad X) ->
    ArithmeticTensorTupleBlock tensorPlaces tensorTuple
  tensorLanding_q : tensorLanding ((nativeQActual X).q :
    Completion (nativeFPlaceOverBad X)) =
    (tensorUnit : ArithmeticTensorTupleBlock tensorPlaces tensorTuple)

/-- Native-pilot donor: all fields live on X.S.arithmetic; q is nativeQActual
at the native F-place, place is nativeC3Place at Fmod. -/
structure NativeSourcePilotRegionDonors where
  p : Nat
  [hp : Fact p.Prime]
  place : FinitePlaceAtPrime X.S.arithmetic.Fmod p
  q : FinitePlaceQCandidate (nativeFPlaceOverBad X)
  thetaPacket : FiniteThetaPacket fiveLabel
  qUnit : (Completion (nativeFPlaceOverBad X))ˣ
  qUnit_eq : qUnit = S3115CandidateUnits X q
  roots : NatRootSystem qUnit
  roots' : NatRootSystem qUnit
  kummerClass : CyclotomicTower (Completion (nativeFPlaceOverBad X))
  rootChange : CyclotomicTower (Completion (nativeFPlaceOverBad X))
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'
  tensorIndex : Type
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex -> Type
  tensorPlaces : (i : tensorIndex) -> tensorPlaceIndex i ->
    FinitePlaceAtPrime X.S.arithmetic.Fmod p
  tensorTuple : (i : tensorIndex) -> tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ
  tensorLanding : Completion (nativeFPlaceOverBad X) ->
    ArithmeticTensorTupleBlock tensorPlaces tensorTuple
  tensorLanding_q : tensorLanding (q.q : Completion (nativeFPlaceOverBad X)) =
    (tensorUnit : ArithmeticTensorTupleBlock tensorPlaces tensorTuple)

attribute [instance] NativeSourcePilotRegionDonors.tensorFintype

/-- Actual conditional construction from explicit BK/BT and S3094Packet. -/
noncomputable def S3115NativeDonor
    (BK : S3115BK X) (BT : S3115BT X)
    (hLp : BT.p = nativeC3Prime X) : NativeSourcePilotRegionDonors X where
  p := BT.p
  hp := BT.hp
  place := hLp.symm ▸ nativeC3Place X
  q := nativeQActual X
  thetaPacket := S3094Packet (T := X.S)
  qUnit := BK.qUnit
  qUnit_eq := BK.qUnit_eq
  roots := BK.roots
  roots' := BK.roots'
  kummerClass := BK.kummerClass
  rootChange := BK.rootChange
  rootChange_eq := BK.rootChange_eq
  tensorIndex := BT.tensorIndex
  tensorFintype := BT.tensorFintype
  tensorPlaceIndex := BT.tensorPlaceIndex
  tensorPlaces := BT.tensorPlaces
  tensorTuple := BT.tensorTuple
  tensorUnit := BT.tensorUnit
  tensorLanding := BT.tensorLanding
  tensorLanding_q := BT.tensorLanding_q

#check S3115BK
#check S3115BT
#check NativeSourcePilotRegionDonors
#check S3115NativeDonor

end LeanFormal.IUT.XiFPaper.S3115NativeSourcePilotRegionDonors
end