import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S859PaperIntrinsicLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Paper intrinsic log-volume on the root-stack section carrier, given by the
actual divisor coordinate and log p. -/
noncomputable def paperIntrinsicLogVolume (u : StackSectionCarrier (l := l) T b) : Real :=
  (stackDivisorSection (l := l) T b u).toAdd *
    Real.log (qVFamTensorP T b : Real)

/-- The actual root section has intrinsic log-volume order/(2l) * log p. -/
theorem paperIntrinsicLogVolume_root :
    paperIntrinsicLogVolume (l := l) T b
        (stackRootSection (l := l) T b) =
      (((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP T b : Real) := by
  unfold paperIntrinsicLogVolume stackDivisorSection stackRootSection
  simp

/-- The actual q section has intrinsic log-volume order * log p. -/
theorem paperIntrinsicLogVolume_q :
    paperIntrinsicLogVolume (l := l) T b
        (stackQSection (l := l) T b) =
      ((qVFamily T b).order : Real) *
        Real.log (qVFamTensorP T b : Real) := by
  unfold paperIntrinsicLogVolume stackDivisorSection stackQSection
  simp

/-- Exact missing datum for the least-hull log: an actual intrinsic log-volume
on the least lambda-O hull, compatible with the section divisor. -/
def PaperLeastHullLogDatum : Prop :=
  ∃ V : Set (rootStackExtension (l := l) T b) → Real,
    V (Metric.closedBall (0 : rootStackExtension (l := l) T b)
        ‖((stackRootSection (l := l) T b).1 :
          rootStackExtension (l := l) T b)‖) =
      paperIntrinsicLogVolume (l := l) T b (stackRootSection (l := l) T b)

end LeanFormal.IUT.XiFPaper.S859PaperIntrinsicLogVolumeActual

end
