import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual

-- S799: paper target on the true least lambda*O hull.
-- S797's rootThetaHull containment is only a union/closure upper bound.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ]

/-- Paper qPilot region at paper-order coefficient: exactly the least lambda*O
region, not the old union closure. -/
noncomputable def paperQPilotRegionLeast : Set (qVFamTensorBlock T b) :=
  paperLambdaORegion (l := l) T b (paperRootCoefficientFamily T b)

theorem paperQPilotRegionLeast_eq_least :
    paperQPilotRegionLeast (l := l) T b = paperLeastLambdaOHull (l := l) T b :=
  (paperLeastLambdaOHull_eq_minimal (l := l) T b).symm

theorem paperQPilotRegionLeast_subset_least :
    paperQPilotRegionLeast (l := l) T b ⊆ paperLeastLambdaOHull (l := l) T b := by
  rw [paperQPilotRegionLeast_eq_least]

/-- Paper qPilot log from the least-hull fractional coefficient. -/
noncomputable def paperQPilotLogLeast : Real :=
  -((∑ _ : qVFamTensorV, paperRootCoefficientFamily T b ()) *
    Real.log (qVFamTensorP T b : Real))

/-- Least lambda*O hull normalized log. -/
noncomputable def paperLeastLambdaOHullLog : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple μ
    (paperLeastLambdaOHull (l := l) T b)

theorem paperLeastLambdaOHullLog_eq_formula
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b)) :
    paperLeastLambdaOHullLog (l := l) T b μ =
      -((∑ _ : qVFamTensorV, paperRootCoefficientFamily T b ()) *
        Real.log (qVFamTensorP T b : Real)) := by
  unfold paperLeastLambdaOHullLog
  rw [paperLeastLambdaOHull_eq_minimal (l := l) T b]
  exact arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (qVFamTensorPlaces T b) qVFamTensorTuple μ data

theorem paperQPilotLogLeast_eq_leastHullLog
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b)) :
    paperQPilotLogLeast (l := l) T b = paperLeastLambdaOHullLog (l := l) T b μ :=
  (paperLeastLambdaOHullLog_eq_formula (l := l) T b μ data).symm

theorem paperQPilotLogLeast_le_leastHullLog
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b)) :
    paperQPilotLogLeast (l := l) T b ≤ paperLeastLambdaOHullLog (l := l) T b μ :=
  le_of_eq (paperQPilotLogLeast_eq_leastHullLog (l := l) T b μ data)

/-- old union/closure hull is only a superset of the true least hull. -/
theorem oldUnionHull_upper_bound :
    paperLeastLambdaOHull (l := l) T b ⊆ paperRootThetaHull T b :=
  paperLeastLambdaOHull_subset_old_unionHull (l := l) T b

#check paperQPilotRegionLeast_subset_least
#check paperLeastLambdaOHullLog_eq_formula
#check paperQPilotLogLeast_le_leastHullLog
#check oldUnionHull_upper_bound

end LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual

end