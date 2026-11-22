import tmp.sheaf.xif.paper.S855OtriLogVolumeInterfaceActual
import tmp.sheaf.xif.paper.S864PaperLambdaOLogVolumeActual
import tmp.sheaf.xif.paper.S859PaperIntrinsicLogVolumeActual

/-! # S867: Otri interface from S859 section V, and S864 lambda-O consistency

For a given mono-analytic log-shell compact carrier D, the Otri interface is
filled by the actual S859 section intrinsic volumes:
  qOrder    = paperIntrinsicLogVolume (stackQSection)
  rootOrder = paperIntrinsicLogVolume (stackRootSection)
  logVolume = paperIntrinsicLogVolume (stackRootSection).
The q/root relation order/(2l) is proved from the S859 formulas, and the
root volume is identified with -paperLambdaOLogVolume(cRoot) via S864.
No carrier and no least-hull volume functional is fabricated. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S867OtriPaperIntegrationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.MonoAnalyticLogShellCompactCarrier
open LeanFormal.IUT.XiFPaper.S855OtriLogVolumeInterfaceActual
open LeanFormal.IUT.XiFPaper.S859PaperIntrinsicLogVolumeActual
open LeanFormal.IUT.XiFPaper.S864PaperLambdaOLogVolumeActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- The S859 root intrinsic volume is -paperLambdaOLogVolume(cRoot). -/
theorem s867_intrinsicRoot_eq_neg_lambdaO :
    paperIntrinsicLogVolume (l := l) T b (stackRootSection (l := l) T b) =
      -paperLambdaOLogVolume (l := l) T b (paperRootCoefficientFamily T b) := by
  have h := paperLambdaOLogVolume_cRoot_eq_neg_section (l := l) T b
  linarith

/-- Actual Otri interface filled by the S859 section V. -/
noncomputable def s867OtriInterface
    (D : MonoAnalyticLogShellCompactCarrier.{0}) :
    OtriLogVolumeInterface (l := l) T b where
  carrier := D
  qOrder := ((qVFamily T b).order : Real)
  rootOrder := ((qVFamily T b).order : Real) / (2 * (l.value : Real))
  qOrder_eq := rfl
  rootOrder_eq := rfl
  logVolume := paperIntrinsicLogVolume (l := l) T b (stackRootSection (l := l) T b)
  logVolume_normalization :=
    paperIntrinsicLogVolume (l := l) T b (stackRootSection (l := l) T b) =
      -paperLambdaOLogVolume (l := l) T b (paperRootCoefficientFamily T b)

/-- Actual consistency of the interface qOrder with the S859 q section. -/
theorem s867_qOrder_mul_log :
    (((qVFamily T b).order : Real) *
        Real.log (qVFamTensorP T b : Real)) =
      paperIntrinsicLogVolume (l := l) T b (stackQSection (l := l) T b) := by
  rw [paperIntrinsicLogVolume_q]

/-- Actual consistency of the interface rootOrder with the S859 root section. -/
theorem s867_rootOrder_mul_log :
    ((((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP T b : Real)) =
      paperIntrinsicLogVolume (l := l) T b (stackRootSection (l := l) T b) := by
  rw [paperIntrinsicLogVolume_root]

/-- Actual interface existence from any carrier. -/
theorem s867OtriInterfaceRequired_of_carrier
    (D : MonoAnalyticLogShellCompactCarrier.{0}) :
    OtriLogVolumeInterfaceRequired (l := l) T b :=
  ⟨s867OtriInterface (l := l) T b D⟩

/-- The interface logVolume normalization holds (S864). -/
theorem s867_logVolume_normalization
    (D : MonoAnalyticLogShellCompactCarrier.{0}) :
    OtriLogVolumeNormalizationRequired (l := l) T b
      (s867OtriInterface (l := l) T b D) := by
  exact s867_intrinsicRoot_eq_neg_lambdaO (l := l) T b

/-- Exact least-hull carrier bridge from S859 to the qVFam lambda-O region:
it is the only missing datum for turning the Otri/S864 consistency into
PaperLeastHullLogDatumQVFam. -/
def S867LeastHullCarrierConsistency : Prop :=
  PaperLeastHullCarrierBridge (l := l) T b

/-- Exact lambda-O least-hull datum. -/
def S867PaperLeastHullLogDatumQVFam : Prop :=
  PaperLeastHullLogDatumQVFam (l := l) T b

end LeanFormal.IUT.XiFPaper.S867OtriPaperIntegrationActual

end
