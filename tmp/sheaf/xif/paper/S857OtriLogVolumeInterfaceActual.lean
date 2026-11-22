import tmp.sheaf.xif.paper.S822PadicDetHullActual
import tmp.sheaf.xif.paper.S799LeastLambdaOPaperTargetActual

/-! # S857: OtriLogVolumeInterface from actual lambda-O log-volume

S822 gives the actual normalized log-volume of the least lambda-O region:
  logVolume(lambdaOSet c) = -sum c * log p,
conditional only on the actual fractional scaling data at c.  With the
paper coefficient order/(2l) this is the paper least-hull log, and S799 gives
qPilotLog = hullLog.  The scaling data is the exact remaining input.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S857OtriLogVolumeInterfaceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S822PadicDetHullActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ]

/-- Interface for the actual Otri lambda-O log-volume on the paper least hull. -/
structure OtriLogVolumeInterface (X : Type*) where
  hull : Set X
  qPilotRegion : Set X
  containment : qPilotRegion ⊆ hull
  lambdaOSet : Set X
  lambdaOSet_eq_hull : lambdaOSet = hull
  logVolume : Set X → Real
  hullLog : Real
  hullLog_eq_logVolume : hullLog = logVolume hull
  lambdaOLog : Real
  lambdaOLog_eq_formula : Prop
  hullLog_eq_lambdaO : hullLog = lambdaOLog
  qPilotLog : Real
  qPilotLog_le_hullLog : qPilotLog ≤ hullLog

/-- Actual interface, conditional only on fractional scaling data at the
paper coefficient order/(2l). -/
noncomputable def otriLogVolumeInterface
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily (l := l) T b)) :
    OtriLogVolumeInterface (qVFamTensorBlock T b) where
  hull := paperLeastLambdaOHull (l := l) T b
  qPilotRegion := paperQPilotRegionLeast (l := l) T b
  containment := paperQPilotRegionLeast_subset_least (l := l) T b
  lambdaOSet := paperLeastLambdaOHull (l := l) T b
  lambdaOSet_eq_hull := rfl
  logVolume := arithmeticTupleNormalizedLogVolume
    (qVFamTensorPlaces T b) qVFamTensorTuple μ
  hullLog := paperLeastLambdaOHullLog (l := l) T b μ
  hullLog_eq_logVolume := rfl
  lambdaOLog := hullLogFunctional (l := l) T b
    (paperRootCoefficientFamily (l := l) T b)
  lambdaOLog_eq_formula :=
    paperLeastLambdaOHullLog (l := l) T b μ =
      -((∑ _ : qVFamTensorV,
          paperRootCoefficientFamily (l := l) T b ()) *
        Real.log (qVFamTensorP T b : Real))
  hullLog_eq_lambdaO := by
    change paperLeastLambdaOHullLog (l := l) T b μ =
      hullLogFunctional (l := l) T b
        (paperRootCoefficientFamily (l := l) T b)
    unfold hullLogFunctional
    exact paperLeastLambdaOHullLog_eq_formula (l := l) T b μ data
  qPilotLog := paperQPilotLogLeast (l := l) T b
  qPilotLog_le_hullLog :=
    paperQPilotLogLeast_le_leastHullLog (l := l) T b μ data

/-- Exact input: scaling data at the paper coefficient. -/
def PaperCoefficientScalingDataRequired : Prop :=
  Nonempty (ArithmeticTuplePureFractionalScalingData
    (qVFamTensorPlaces T b) qVFamTensorTuple
    (paperRootCoefficientFamily (l := l) T b))

end LeanFormal.IUT.XiFPaper.S857OtriLogVolumeInterfaceActual
end
