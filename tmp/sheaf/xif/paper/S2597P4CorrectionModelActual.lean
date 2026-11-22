import tmp.sheaf.xif.paper.S2596P4ScalingCorrectionActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual

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

namespace LeanFormal.IUT.XiFPaper.S2597P4CorrectionModelActual

universe ua upi umon ui

variable {l : PrimeGeFive}
variable (S : SourceDefinition31Data.{ua} l)
variable (n : ThetaPilotCarrier l)
variable (T : SourceNativeInitialThetaData l)
variable (β : Bad (nativePlaceSelection T))

/-- The model source input of `SourceUnitRegionHaarDataActual`. -/
abbrev P4ModelI (S : SourceDefinition31Data.{ua} l) :
    OriginalInput.{ua, 0, 0, 0, 0} l Unit :=
  sourceHaarActualOriginalInput (l := l) S

/-- The model image realization. -/
abbrev P4ModelR (S : SourceDefinition31Data.{ua} l) :
    (P4ModelI S).SourceImageRealization () :=
  sourceHaarActualImageRealization (l := l) S

/-- The model unit-region/Haar datum, whose scaling is literally `1`. -/
abbrev P4ModelD (S : SourceDefinition31Data.{ua} l) (n : ThetaPilotCarrier l) :
    (P4ModelI S).SourceUnitRegionHaarData () (P4ModelR S) n :=
  sourceHaarActualData (l := l) S n

/-- **Actual correction instance**: the concrete nonpositive-value model has
scaling `1`, hence zero source local log-degree, so the S2593 unscaled
dictionary converts to the frozen scaled dictionary. -/
theorem P4Model_scalingCorrection
    (S : SourceDefinition31Data.{ua} l) (n : ThetaPilotCarrier l) :
    P4ScalingDegreeCorrection (P4ModelI S) () (P4ModelR S) n (P4ModelD S n) := by
  apply P4ScalingDegreeCorrection_of_scaling_eq_one
  exact sourceHaarActualData_scaling (l := l) S n

/-- Actual conversion of the unscaled S2593 dictionary to the frozen scaled
dictionary on the concrete model. -/
theorem P4Model_scaledCandidateDictionary
    (S : SourceDefinition31Data.{ua} l) (n : ThetaPilotCarrier l)
    (T : SourceNativeInitialThetaData l)
    (β : Bad (nativePlaceSelection T))
    (h : P4SourceLogDegreeDictionary (P4ModelI S) (P4ModelR S) T β) :
    P4ScaledCandidateDictionary (P4ModelI S) () (P4ModelR S) n
      (P4ModelD S n) T β := by
  exact P4ScaledCandidateDictionary_of_source (P4ModelI S) () (P4ModelR S) n
    (P4ModelD S n) T β (P4Model_scalingCorrection S n) h

#print axioms P4Model_scalingCorrection
#print axioms P4Model_scaledCandidateDictionary

end LeanFormal.IUT.XiFPaper.S2597P4CorrectionModelActual
end
