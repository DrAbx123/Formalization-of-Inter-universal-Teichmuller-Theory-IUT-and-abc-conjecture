import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.NativeInput

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3111DonorFPlaceAuditAdapted

/-- A donor generalized to an arbitrary base field B. -/
structure S3111GeneralizedDonor (l : PrimeGeFive) (B : Type)
    [Field B] [NumberField B] where
  p : Nat
  [hp : Fact p.Prime]
  place : FinitePlaceAtPrime B p
  q : FinitePlaceQCandidate place.val
  thetaPacket : FiniteThetaPacket l
  qUnit : (CommonPrimeCompletion place)ˣ
  qUnit_eq : qUnit = candidateUnits place q
  roots : NatRootSystem qUnit
  roots' : NatRootSystem qUnit
  kummerClass : CyclotomicTower (CommonPrimeCompletion place)
  rootChange : CyclotomicTower (CommonPrimeCompletion place)
  rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'
  tensorIndex : Type
  [tensorFintype : Fintype tensorIndex]
  tensorPlaceIndex : tensorIndex -> Type
  tensorPlaces : (i : tensorIndex) -> tensorPlaceIndex i -> FinitePlaceAtPrime B p
  tensorTuple : (i : tensorIndex) -> tensorPlaceIndex i
  tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ
  tensorLanding : CommonPrimeCompletion place ->
    ArithmeticTensorTupleBlock tensorPlaces tensorTuple
  tensorLanding_q : tensorLanding (q.q : CommonPrimeCompletion place) =
    (tensorUnit : ArithmeticTensorTupleBlock tensorPlaces tensorTuple)

attribute [instance] S3111GeneralizedDonor.hp
attribute [instance] S3111GeneralizedDonor.tensorFintype

/-- Any old donor is a generalized donor over B = Fmod. -/
noncomputable def S3111GeneralizedOfDonor
    {l : PrimeGeFive} {V : Type} (I : OriginalInput l V)
    (D : SourcePilotRegionData (l := l) (V := V) I) :
    S3111GeneralizedDonor l (I.initial.arithmetic.Fmod) where
  p := D.p
  hp := D.hp
  place := D.place
  q := D.q
  thetaPacket := D.thetaPacket
  qUnit := D.qUnit
  qUnit_eq := D.qUnit_eq
  roots := D.roots
  roots' := D.roots'
  kummerClass := D.kummerClass
  rootChange := D.rootChange
  rootChange_eq := D.rootChange_eq
  tensorIndex := D.tensorIndex
  tensorFintype := D.tensorFintype
  tensorPlaceIndex := D.tensorPlaceIndex
  tensorPlaces := D.tensorPlaces
  tensorTuple := D.tensorTuple
  tensorUnit := D.tensorUnit
  tensorLanding := D.tensorLanding
  tensorLanding_q := D.tensorLanding_q

/-- Exact F-side donor target for the native F field instead of Fmod. -/
def S3111FDonorTarget (X : N8NativeInput fiveLabel) : Prop :=
  Nonempty (S3111GeneralizedDonor fiveLabel X.S.arithmetic.F)

/-- Base-field equality that would be needed to regard the old donor as F-side. -/
def S3111BaseFieldEq (X : N8NativeInput fiveLabel)
    (I : OriginalInput fiveLabel (FinitePrimePlace 2 7)) : Prop :=
  I.initial.arithmetic.Fmod = X.S.arithmetic.F

#check S3111GeneralizedDonor
#check S3111GeneralizedOfDonor
#check S3111FDonorTarget
#check S3111BaseFieldEq

end LeanFormal.IUT.XiFPaper.S3111DonorFPlaceAuditAdapted
end