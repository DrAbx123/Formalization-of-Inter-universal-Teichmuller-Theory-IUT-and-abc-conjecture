import tmp.sheaf.xif.paper.S3132ThetaSideClauseResidualActual
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
open LeanFormal.IUT.XiFPaper.S3136ModelClauseWitnessAdapterActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideClauseResidualActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedPilotComparisonActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedCorollary312DataActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideClauseComparisonDataActual

/-! # Paper-route Theta side: comparison data from the clause-data readout

The adapted Corollary 3.12 comparison payload whose Theta-side signed entry is the
negative of the clause-data canonical rooted readout (the positive-magnitude H_C
value).  Conditional exactly on the clause data + V-form residual; the q-side
signed value and the signed comparison are explicit hypotheses (q-side stream).
Component, not a paper object. -/

variable {l : PrimeGeFive}
variable (M : LGPConcreteClauseData l)
variable [Fintype (Bad (nativePlaceSelection (lgpConcreteClauseData_toNativeData M)))]

/-- The clause-data canonical rooted Theta value. -/
noncomputable def clauseThetaValue : ℝ :=
  S3131CanonicalRootedHC (l := l)
    (clauseNativeData (l := l) M) (clauseHaar (l := l) M)

/-- The clause-data comparison payload (Theta signed = negative canonical value). -/
def clauseComparisonData (qSigned : ℝ) (hq : 0 < -qSigned)
    (hle : qSigned ≤ -clauseThetaValue (l := l) M) :
    AdaptedCorollary312ComparisonData :=
  { thetaSigned := -clauseThetaValue (l := l) M
    qSigned := qSigned
    q_positive := hq
    qSigned_le_thetaSigned := hle }

/-- Its Theta pilot magnitude is the canonical clause-data readout. -/
theorem clauseComparisonData_thetaPilot_value (qSigned : ℝ)
    (hq : 0 < -qSigned) (hle : qSigned ≤ -clauseThetaValue (l := l) M) :
    (clauseComparisonData (l := l) M qSigned hq hle).thetaPilot.value =
      clauseThetaValue (l := l) M := by
  simp [clauseComparisonData, AdaptedCorollary312ComparisonData.thetaPilot,
    adaptedSignedPilotLogVolume]

/-- Its q pilot magnitude is the positive q value. -/
theorem clauseComparisonData_qPilot_value (qSigned : ℝ)
    (hq : 0 < -qSigned) (hle : qSigned ≤ -clauseThetaValue (l := l) M) :
    (clauseComparisonData (l := l) M qSigned hq hle).qPilot.value = -qSigned := by
  simp [clauseComparisonData, AdaptedCorollary312ComparisonData.qPilot,
    adaptedSignedPilotLogVolume]

/-- The clause-data payload satisfies the adapted Corollary 3.12 inequality. -/
theorem clauseComparisonData_corollary312 (qSigned : ℝ)
    (hq : 0 < -qSigned) (hle : qSigned ≤ -clauseThetaValue (l := l) M) :
    AdaptedCorollary312Inequality
      (clauseComparisonData (l := l) M qSigned hq hle).thetaPilot
      (clauseComparisonData (l := l) M qSigned hq hle).qPilot :=
  AdaptedCorollary312ComparisonData.corollary312 _

#check clauseThetaValue
#check clauseComparisonData
#check clauseComparisonData_thetaPilot_value
#check clauseComparisonData_corollary312

end LeanFormal.IUT.XiFPaper.S3132ThetaSideClauseComparisonDataActual
end
