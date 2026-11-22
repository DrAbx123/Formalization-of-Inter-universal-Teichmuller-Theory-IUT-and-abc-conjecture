import tmp.sheaf.xif.paper.S3117AlgC3Attempt
import tmp.sheaf.xif.paper.S2757CanonicalGaussianTActual
import tmp.sheaf.xif.paper.S2757SourceCompletionNativeActual
import tmp.sheaf.xif.paper.S2726TensorIndexBridgeTarget
import tmp.sheaf.xif.paper.S2727ABCConjectureOfActualInputs
noncomputable section
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.XiFPaper.S3117AlgC3Attempt
open LeanFormal.IUT.XiFPaper.S2757CanonicalGaussianTActual
open LeanFormal.IUT.XiFPaper.S2757SourceCompletionNativeActual
open LeanFormal.IUT.XiFPaper.S2726TensorComparisonRegionRhoActual
open LeanFormal.IUT.XiFPaper.S2727ABCConjectureOfActualInputs
namespace LeanFormal.IUT.XiFPaper.S2727ActualInputCandidates

/-! ## S2727 `ABCConjecture_of_actual_inputs` input candidate table

| input | actual candidate | status |
| C3 | `S3117AlgC3Attempt.actualSignedC3Alg` / `SourcePilotRegionDataAlg` | donor-level actual; needs bridge to `SourcePilotRegionData I` |
| T | `S2757CanonicalGaussianT C h` or `S2757NativeT A G P assembly` | actual conditional on `SourceCompletion` / clause assembly |
| e | `S2726TensorIndexBridgeTarget C3 T` | only `Prop` (`Nonempty` of equivalence), not an actual equivalence |
| A | — | missing (additive constant function) |
| logShellPoint+mem | — | missing (point in comparisonRegion) |
| hheight | — | missing (arithmetic height gap) |
| hvol | — | missing (volume/weight gap) |
-/

#check SourcePilotRegionDataAlg
#check S3117AlgC3Attempt.actualSignedC3Alg
#check S2757CanonicalGaussianT
#check S2757NativeT
#check S2726TensorIndexBridgeTarget
#check ABCConjecture_of_actual_inputs

end LeanFormal.IUT.XiFPaper.S2727ActualInputCandidates