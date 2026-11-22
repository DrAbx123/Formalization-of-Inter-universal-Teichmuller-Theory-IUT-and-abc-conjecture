import tmp.sheaf.xif.paper.S2593P4CandidateActual
import tmp.sheaf.xif.paper.S2590P4SourceDictionaryActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapSupplyLayer
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S2593P4CandidateActual
open LeanFormal.IUT.XiFPaper.S2590P4SourceDictionaryActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2595P4WiringActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (D : I.SourceUnitRegionHaarData v R n)
variable (T : SourceNativeInitialThetaData l)
variable (β : Bad (nativePlaceSelection T))

/-- The P4 candidate dictionary scaled by the actual source unit-region
scaling `D.scaling`, exactly the frozen `hweightvol` input. -/
def P4ScaledCandidateDictionary : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    arithmeticWeight (abcRationalPoint a c) <=
      I.sourceLocalLogDegree v
        (D.scaling * P4CandidatePoint I R T β a b c)

/-- **P4 wiring**: the scaled S2593 candidate dictionary instantiates the frozen
source weight-volume theorem, giving the exact `hweightvol` input at the actual
value-realized carrier. -/
theorem P4_hweightvol_of_scaledCandidate
    (h : P4ScaledCandidateDictionary I v R n D T β) :
    forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        ((I.sourceUnitRegionHaarInterface v R n D).logVolume
          (normalizedComparisonRegion (I.sourceUnitRegionHaarInterface v R n D)
            (fun a b c => P4CandidatePoint I R T β a b c) a b c)).toReal :=
  I.cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary
    v R n D (fun a b c => P4CandidatePoint I R T β a b c) h

/-- **P4 wired back to the Cor 3.12 comparison consumer.** Given the other four
reduced gap inputs (`hval`,`hunit`,`hsplit`,`hptfin`,`hpoint`), the scaled P4
candidate dictionary fills the weight-volume field and yields an actual
`Cor312EpsilonArithmeticComparison` at the value-realized source carrier. -/
noncomputable def P4_epsilonComparison_of_reducedInputs
    {eps D0 D1 : Real} (heps : 0 <= eps) (hD0 : 0 <= D0)
    (hval : forall a b c : Nat, IsABCTriple a b c ->
      forall q, q ∈ arithmeticPrimeSupport (abcRationalPoint a c) ->
        max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) <= 1 + eps)
    (hP4 : P4ScaledCandidateDictionary I v R n D T β)
    (hunit : (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (I.sourceUnitRegionHaarInterface v R n D).unitRegion <=
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (I.sourceUnitRegionHaarInterface v R n D).hull + ENNReal.ofReal D0)
    (hsplit : forall a b c : Nat, IsABCTriple a b c ->
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
          (normalizedComparisonRegion (I.sourceUnitRegionHaarInterface v R n D)
            (fun a b c => P4CandidatePoint I R T β a b c) a b c) <=
        (I.sourceUnitRegionHaarInterface v R n D).logVolume
            ((I.sourceUnitRegionHaarInterface v R n D).scaleShift ''
              (I.sourceUnitRegionHaarInterface v R n D).unitRegion) +
          (I.sourceUnitRegionHaarInterface v R n D).logVolume
            {(I.sourceUnitRegionHaarInterface v R n D).scaleShift (P4CandidatePoint I R T β a b c)})
    (hptfin : forall a b c : Nat, IsABCTriple a b c ->
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
        {(I.sourceUnitRegionHaarInterface v R n D).scaleShift (P4CandidatePoint I R T β a b c)} < ⊤)
    (hpoint : forall a b c : Nat, IsABCTriple a b c ->
      ((I.sourceUnitRegionHaarInterface v R n D).logVolume
        {(I.sourceUnitRegionHaarInterface v R n D).scaleShift (P4CandidatePoint I R T β a b c)}).toReal <=
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D1) :
    Cor312EpsilonArithmeticComparison (I.sourceUnitRegionHaarInterface v R n D) eps :=
  cor312GapAssembly_epsilonComparisonOfReducedInputs
    (I.sourceUnitRegionHaarInterface v R n D)
    (fun a b c => P4CandidatePoint I R T β a b c) heps hD0 hval
    (by
      intro a b c habc
      have hw := P4_hweightvol_of_scaledCandidate I v R n D T β hP4 a b c habc
      -- the two `p` choices are definitionally the same after unfolding the map
      simpa only using hw)
    hunit hsplit hptfin hpoint

#print axioms P4_hweightvol_of_scaledCandidate
#print axioms P4_epsilonComparison_of_reducedInputs

end LeanFormal.IUT.XiFPaper.S2595P4WiringActual
end
