import tmp.sheaf.xif.paper.S2596P4ScalingCorrectionActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.OModuleCompactnessLayer
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceContractedSupplyRealization

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S2593P4CandidateActual
open LeanFormal.IUT.XiFPaper.S2596P4ScalingCorrectionActual
open LeanFormal.IUT.XiFPaper.S2595P4WiringActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2598PaperDCorrectionActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (T : SourceNativeInitialThetaData l)
variable (β : Bad (nativePlaceSelection T))

/-- **Paper D from the compactness premise.**
`sourceOModuleCompactness_haarData` has scaling literally `1`; hence its
source local log-degree is zero and the S2596 correction applies. -/
theorem P4_paperCorrection_of_compactness
    (C : I.SourceOneCircUCompactness v R n) :
    P4ScalingDegreeCorrection I v R n
      (I.sourceOModuleCompactness_haarData v R n C) := by
  apply P4ScalingDegreeCorrection_of_scaling_eq_one
  exact I.sourceOModuleCompactness_haarData_scaling v R n C

/-- Unscaled S2593 dictionary converts to the frozen scaled dictionary at the
paper compactness D. -/
theorem P4_paperScaledCandidateDictionary_of_compactness
    (C : I.SourceOneCircUCompactness v R n)
    (h : P4SourceLogDegreeDictionary I R T β) :
    P4ScaledCandidateDictionary I v R n
      (I.sourceOModuleCompactness_haarData v R n C) T β := by
  exact P4ScaledCandidateDictionary_of_source I v R n
    (I.sourceOModuleCompactness_haarData v R n C) T β
    (P4_paperCorrection_of_compactness I v R n C) h

/-- **Paper D from contracted generators.**
`sourceContractedUnitRegionHaarData` also has scaling `1`. -/
theorem P4_paperCorrection_of_contracted
    (hImage : forall j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) <= 0)
    (hScaling : forall s, s ∈ I.sourceScalingUnits v ->
      I.sourceLocalLogDegree v s <= 0) :
    P4ScalingDegreeCorrection I v R n
      (I.sourceContractedUnitRegionHaarData v R n hImage hScaling) := by
  apply P4ScalingDegreeCorrection_of_scaling_eq_one
  rfl

/-- Unscaled S2593 dictionary converts to the frozen scaled dictionary at the
paper contracted D. -/
theorem P4_paperScaledCandidateDictionary_of_contracted
    (hImage : forall j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) <= 0)
    (hScaling : forall s, s ∈ I.sourceScalingUnits v ->
      I.sourceLocalLogDegree v s <= 0)
    (h : P4SourceLogDegreeDictionary I R T β) :
    P4ScaledCandidateDictionary I v R n
      (I.sourceContractedUnitRegionHaarData v R n hImage hScaling) T β := by
  exact P4ScaledCandidateDictionary_of_source I v R n
    (I.sourceContractedUnitRegionHaarData v R n hImage hScaling) T β
    (P4_paperCorrection_of_contracted I v R n hImage hScaling) h

#print axioms P4_paperCorrection_of_compactness
#print axioms P4_paperScaledCandidateDictionary_of_compactness
#print axioms P4_paperCorrection_of_contracted
#print axioms P4_paperScaledCandidateDictionary_of_contracted

end LeanFormal.IUT.XiFPaper.S2598PaperDCorrectionActual
end
