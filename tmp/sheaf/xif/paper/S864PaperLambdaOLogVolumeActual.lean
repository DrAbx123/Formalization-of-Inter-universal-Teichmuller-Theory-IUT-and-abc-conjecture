import tmp.sheaf.xif.paper.S859PaperIntrinsicLogVolumeActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S864PaperLambdaOLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S859PaperIntrinsicLogVolumeActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Paper log-shell intrinsic log on a lambda-O exponent vector. -/
noncomputable def paperLambdaOLogVolume (lam : qVFamTensorV → Real) : Real :=
  -((∑ _ : qVFamTensorV, lam ()) * Real.log (qVFamTensorP T b : Real))

/-- At the paper root coefficient this is -sum(cRoot) log p. -/
theorem paperLambdaOLogVolume_cRoot :
    paperLambdaOLogVolume (l := l) T b (paperRootCoefficientFamily T b) =
      -((∑ _ : qVFamTensorV, paperRootCoefficientFamily T b ()) *
        Real.log (qVFamTensorP T b : Real)) := rfl

/-- Exact sign relation to the S859 section intrinsic volume at the root section. -/
theorem paperLambdaOLogVolume_cRoot_eq_neg_section :
    paperLambdaOLogVolume (l := l) T b (paperRootCoefficientFamily T b) =
      -paperIntrinsicLogVolume (l := l) T b
        (stackRootSection (l := l) T b) := by
  unfold paperLambdaOLogVolume paperIntrinsicLogVolume stackDivisorSection
    stackRootSection paperRootCoefficientFamily qVFamPaperRootCoefficient
  simp

/-- Exact missing carrier bridge: S859's datum lives on the root-stack extension,
while the least lambda-O region lives on the qVFam completion block. -/
def PaperLeastHullCarrierBridge : Prop :=
  ∃ V : Set (rootStackExtension (l := l) T b) → Real,
    V (Metric.closedBall (0 : rootStackExtension (l := l) T b)
        ‖((stackRootSection (l := l) T b).1 :
          rootStackExtension (l := l) T b)‖) =
      -paperLambdaOLogVolume (l := l) T b (paperRootCoefficientFamily T b)

/-- Exact corrected least-hull log datum on the qVFam lambda-O region. -/
def PaperLeastHullLogDatumQVFam : Prop :=
  ∃ V : Set (qVFamTensorBlock T b) → Real,
    V (paperLeastLambdaOHull (l := l) T b) =
      paperLambdaOLogVolume (l := l) T b (paperRootCoefficientFamily T b)

/-- Exact sign correction needed for S859's positive convention. -/
def SignCorrectionNeeded : Prop :=
  paperIntrinsicLogVolume (l := l) T b (stackRootSection (l := l) T b) =
    -paperIntrinsicLogVolume (l := l) T b (stackRootSection (l := l) T b)

end LeanFormal.IUT.XiFPaper.S864PaperLambdaOLogVolumeActual

end
