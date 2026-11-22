import tmp.sheaf.xif.paper.S2598PaperDCorrectionActual
import tmp.sheaf.xif.paper.S2595P4WiringActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S2593P4CandidateActual
open LeanFormal.IUT.XiFPaper.S2595P4WiringActual
open LeanFormal.IUT.XiFPaper.S2596P4ScalingCorrectionActual
open LeanFormal.IUT.XiFPaper.S2598PaperDCorrectionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2599PaperP4WiringActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (T : SourceNativeInitialThetaData l)
variable (β : Bad (nativePlaceSelection T))

/-- **Paper-source P4 wiring from compactness**: the S2593 candidate, unscaled
source dictionary, and paper compactness D produce the exact `hweightvol` at
the actual paper value-realized carrier. -/
theorem P4_paper_hweightvol_of_compactness
    (C : I.SourceOneCircUCompactness v R n)
    (h : P4SourceLogDegreeDictionary I R T β) :
    forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        ((I.sourceUnitRegionHaarInterface v R n
            (I.sourceOModuleCompactness_haarData v R n C)).logVolume
          (normalizedComparisonRegion
            (I.sourceUnitRegionHaarInterface v R n
              (I.sourceOModuleCompactness_haarData v R n C))
            (fun a b c => P4CandidatePoint I R T β a b c) a b c)).toReal := by
  exact P4_hweightvol_of_scaledCandidate I v R n
    (I.sourceOModuleCompactness_haarData v R n C) T β
    (P4_paperScaledCandidateDictionary_of_compactness I v R n T β C h)

/-- **Paper-source P4 wiring from contracted generators**. -/
theorem P4_paper_hweightvol_of_contracted
    (hImage : forall j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) <= 0)
    (hScaling : forall s, s ∈ I.sourceScalingUnits v ->
      I.sourceLocalLogDegree v s <= 0)
    (h : P4SourceLogDegreeDictionary I R T β) :
    forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        ((I.sourceUnitRegionHaarInterface v R n
            (I.sourceContractedUnitRegionHaarData v R n hImage hScaling)).logVolume
          (normalizedComparisonRegion
            (I.sourceUnitRegionHaarInterface v R n
              (I.sourceContractedUnitRegionHaarData v R n hImage hScaling))
            (fun a b c => P4CandidatePoint I R T β a b c) a b c)).toReal := by
  exact P4_hweightvol_of_scaledCandidate I v R n
    (I.sourceContractedUnitRegionHaarData v R n hImage hScaling) T β
    (P4_paperScaledCandidateDictionary_of_contracted I v R n T β hImage hScaling h)

#print axioms P4_paper_hweightvol_of_compactness
#print axioms P4_paper_hweightvol_of_contracted

end LeanFormal.IUT.XiFPaper.S2599PaperP4WiringActual
end
