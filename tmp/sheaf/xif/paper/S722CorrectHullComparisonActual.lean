import tmp.sheaf.xif.paper.S706ThetaPilotHullLogActual
import tmp.sheaf.xif.paper.S707ThetaHullVsThetaValueActual

/-! # S722: correct Theta-hull vs qPilot comparison

S714 compared a finite theta-value average `paperThetaAverage` with the local
qPilot coefficient.  That is a surrogate, not the paper Theta object.
Paper -|log Theta| is the global Theta-pilot hull log (S706), and Cor3.12
compares globalQPilotLog <= globalThetaPilotHullLog, equivalently
thetaPilotMagnitude <= qPilotMagnitude.  A per-b theta-value average being
larger than the local qPilot does not contradict Cor3.12. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S722CorrectHullComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S706ThetaPilotHullLogActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]


/-- Actual correct Cor3.12 hull comparison from S706. -/
theorem correct_thetaPilotMagnitude_le_qPilotMagnitude
    [instM : ∀ b : Bad (nativePlaceSelection T), MeasurableSpace (QVFamTensorCoefficientActual.qVFamTensorBlock T b)]
    [instB : ∀ b : Bad (nativePlaceSelection T), BorelSpace (QVFamTensorCoefficientActual.qVFamTensorBlock T b)] :
    thetaPilotMagnitude (l := l) T ≤ qPilotMagnitude (l := l) T :=
  thetaPilotQpilotComparison (l := l) T

/-- Actual global signed hull comparison from S706. -/
theorem correct_globalComparison
    [instM : ∀ b : Bad (nativePlaceSelection T), MeasurableSpace (QVFamTensorCoefficientActual.qVFamTensorBlock T b)]
    [instB : ∀ b : Bad (nativePlaceSelection T), BorelSpace (QVFamTensorCoefficientActual.qVFamTensorBlock T b)] :
    globalQPilotLog (l := l) T ≤ globalThetaPilotHullLog (l := l) T :=
  (thetaPilotLogVolumeData (l := l) T).comparison

end LeanFormal.IUT.XiFPaper.S722CorrectHullComparisonActual

end
