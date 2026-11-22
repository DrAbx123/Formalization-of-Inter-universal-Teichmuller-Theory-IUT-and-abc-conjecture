import tmp.sheaf.xif.paper.S3132ThetaSideClauseComparisonDataActual
import tmp.sheaf.xif.paper.S3132ThetaSideCanonicalSubsingletonActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual

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
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideCanonicalSubsingletonActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideClauseResidualActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideClauseComparisonDataActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedPilotComparisonActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedCorollary312DataActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideSubsingletonComparisonActual

/-! # Paper-route Theta side: singleton bad-index evaluation of the readout

When the concrete clause data has a one-point native bad family (the minimal
Example 3.6 case), the canonical rooted readout collapses to the unique weighted
rooted tensor V-form term, so the comparison payload's Theta magnitude is an
explicit weight * rooted-V-form value (the evaluation itself has no residual).
Component, not a paper object. -/

variable {l : PrimeGeFive}
variable (M : LGPConcreteClauseData l)
variable [Fintype (Bad (nativePlaceSelection (lgpConcreteClauseData_toNativeData M)))]
variable [Subsingleton (Bad (nativePlaceSelection (lgpConcreteClauseData_toNativeData M)))]
variable (b0 : Bad (nativePlaceSelection (lgpConcreteClauseData_toNativeData M)))

/-- In the singleton case the clause Theta value is the unique weighted rooted
tensor V-form term. -/
theorem clauseThetaValue_of_subsingleton :
    clauseThetaValue (l := l) M =
      nativeBadLocalWeight (lgpConcreteClauseData_toNativeData M) b0 *
        rootThetaHullLog (l := l)
          (qVFamTensorPlaces (lgpConcreteClauseData_toNativeData M) b0)
          qVFamTensorTuple
          (lgpNativeHaarFamily (lgpConcreteClauseData_toNativeData M) b0)
          (rootHalfCoefficient (l := l) (lgpConcreteClauseData_toNativeData M) b0) := by
  unfold clauseThetaValue
  exact canonicalRootedHC_of_subsingleton
    (T := lgpConcreteClauseData_toNativeData M)
    (mu := lgpNativeHaarFamily (lgpConcreteClauseData_toNativeData M)) b0

/-- The comparison payload's Theta pilot magnitude in the singleton case is the
explicit weighted rooted tensor V-form. -/
theorem clauseComparisonData_thetaPilot_value_eq_weight (qSigned : ℝ)
    (hq : 0 < -qSigned) (hle : qSigned ≤ -clauseThetaValue (l := l) M) :
    (clauseComparisonData (l := l) M qSigned hq hle).thetaPilot.value =
      nativeBadLocalWeight (lgpConcreteClauseData_toNativeData M) b0 *
        rootThetaHullLog (l := l)
          (qVFamTensorPlaces (lgpConcreteClauseData_toNativeData M) b0)
          qVFamTensorTuple
          (lgpNativeHaarFamily (lgpConcreteClauseData_toNativeData M) b0)
          (rootHalfCoefficient (l := l) (lgpConcreteClauseData_toNativeData M) b0) := by
  rw [clauseComparisonData_thetaPilot_value]
  exact clauseThetaValue_of_subsingleton (l := l) M b0

#check clauseThetaValue_of_subsingleton
#check clauseComparisonData_thetaPilot_value_eq_weight

end LeanFormal.IUT.XiFPaper.S3132ThetaSideSubsingletonComparisonActual
end
