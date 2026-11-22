import tmp.sheaf.xif.paper.S3132ThetaSideModelClauseResidualActual
import tmp.sheaf.xif.paper.S3132SourceAdaptedCorollary312DataActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideModelClauseResidualActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedPilotComparisonActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedCorollary312DataActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideModelComparisonDataActual

/-! # Paper-route Theta side: comparison data from the minimal model clause data

The adapted Corollary 3.12 comparison payload built from the minimal data
`LGPModelSourceClauseMissing` + concrete Haar family, with the Theta signed entry
the negative of the canonical rooted readout.  Component, not a paper object. -/

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- The model-side canonical rooted Theta value. -/
noncomputable def modelThetaValue : ℝ :=
  S3131CanonicalRootedHC (l := l)
    (modelNativeData (l := l) M)
    (lgpNativeHaarFamily (modelNativeData (l := l) M))

/-- The model-side comparison payload. -/
def modelComparisonData (qSigned : ℝ) (hq : 0 < -qSigned)
    (hle : qSigned ≤ -modelThetaValue (l := l) M) :
    AdaptedCorollary312ComparisonData :=
  { thetaSigned := -modelThetaValue (l := l) M
    qSigned := qSigned
    q_positive := hq
    qSigned_le_thetaSigned := hle }

/-- Its Theta pilot magnitude is the canonical model readout. -/
theorem modelComparisonData_thetaPilot_value (qSigned : ℝ)
    (hq : 0 < -qSigned) (hle : qSigned ≤ -modelThetaValue (l := l) M) :
    (modelComparisonData (l := l) M qSigned hq hle).thetaPilot.value =
      modelThetaValue (l := l) M := by
  simp [modelComparisonData, AdaptedCorollary312ComparisonData.thetaPilot,
    adaptedSignedPilotLogVolume]

/-- Its q pilot magnitude is the positive q value. -/
theorem modelComparisonData_qPilot_value (qSigned : ℝ)
    (hq : 0 < -qSigned) (hle : qSigned ≤ -modelThetaValue (l := l) M) :
    (modelComparisonData (l := l) M qSigned hq hle).qPilot.value = -qSigned := by
  simp [modelComparisonData, AdaptedCorollary312ComparisonData.qPilot,
    adaptedSignedPilotLogVolume]

/-- The model-side payload satisfies the adapted Corollary 3.12 inequality. -/
theorem modelComparisonData_corollary312 (qSigned : ℝ)
    (hq : 0 < -qSigned) (hle : qSigned ≤ -modelThetaValue (l := l) M) :
    AdaptedCorollary312Inequality
      (modelComparisonData (l := l) M qSigned hq hle).thetaPilot
      (modelComparisonData (l := l) M qSigned hq hle).qPilot :=
  AdaptedCorollary312ComparisonData.corollary312 _

#check modelThetaValue
#check modelComparisonData
#check modelComparisonData_thetaPilot_value
#check modelComparisonData_corollary312

end LeanFormal.IUT.XiFPaper.S3132ThetaSideModelComparisonDataActual
end
