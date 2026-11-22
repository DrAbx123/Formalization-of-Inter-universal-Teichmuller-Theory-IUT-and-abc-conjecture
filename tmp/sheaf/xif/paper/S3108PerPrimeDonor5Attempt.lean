import tmp.sheaf.n8.closure.C3Actual
import tmp.sheaf.n8.closure.C3Roots
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.S3108PerPrimeDonor5Attempt

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

variable {l : PrimeGeFive} {V : Type}
variable (I : OriginalInput l V)

variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) 5)
variable (q : FinitePlaceQCandidate place.val)
variable (thetaPacket : FiniteThetaPacket l)
variable (roots roots' : NatRootSystem (candidateUnits place q))
variable (kummerClass rootChange : CyclotomicTower (CommonPrimeCompletion place))
variable (rootChange_eq :
  rootChange = KummerClass.rootSystemDiff roots roots')
variable (tensorIndex : Type) [Fintype tensorIndex]
variable (tensorPlaceIndex : tensorIndex -> Type)
variable (tensorPlaces : (i : tensorIndex) -> tensorPlaceIndex i ->
  FinitePlaceAtPrime (I.initial.arithmetic.Fmod) 5)
variable (tensorTuple : (i : tensorIndex) -> tensorPlaceIndex i)
variable (tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)ˣ)
variable (tensorLanding : CommonPrimeCompletion place ->
  ArithmeticTensorTupleBlock tensorPlaces tensorTuple)
variable (tensorLanding_q : tensorLanding
  (q.q : CommonPrimeCompletion place) =
  (tensorUnit : ArithmeticTensorTupleBlock tensorPlaces tensorTuple))

/-- Actual donor at p=5 from the explicit base place/q/roots/tensor fields. -/
noncomputable def S3108Donor5 : SourcePilotRegionDonors (l := l) (V := V) I where
  p := 5
  hp := ⟨by norm_num⟩
  place := place
  q := q
  thetaPacket := thetaPacket
  roots := roots
  roots' := roots'
  kummerClass := kummerClass
  rootChange := rootChange
  rootChange_eq := rootChange_eq
  tensorIndex := tensorIndex
  tensorFintype := inferInstance
  tensorPlaceIndex := tensorPlaceIndex
  tensorPlaces := tensorPlaces
  tensorTuple := tensorTuple
  tensorUnit := tensorUnit
  tensorLanding := tensorLanding
  tensorLanding_q := tensorLanding_q

/-- The constructed donor has p = 5 definitionally. -/
theorem S3108Donor5_p :
    (S3108Donor5 I place q thetaPacket roots roots' kummerClass rootChange
      rootChange_eq tensorIndex tensorPlaceIndex tensorPlaces tensorTuple
      tensorUnit tensorLanding tensorLanding_q).p = 5 := rfl

#check S3108Donor5
#check S3108Donor5_p

end LeanFormal.IUT.XiFPaper.S3108PerPrimeDonor5Attempt
end