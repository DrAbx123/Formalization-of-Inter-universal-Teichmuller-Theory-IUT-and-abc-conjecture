import tmp.sheaf.xif.paper.S779RootHullNonzeroFixActual
import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
import tmp.sheaf.xif.paper.S799LeastLambdaOPaperTargetActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S900PerBThetaHullLogNonzeroActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The j=1 minimal region is closed: it is a finite-dimensional Qp-submodule. -/
theorem rootMinimalRegion_closed :
    IsClosed (rootMinimalRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily (l := l) T b) (oneLabel l)) := by
  unfold rootMinimalRegion rootThetaRegion
  change IsClosed (((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
    qVFamTensorTuple (fun i => ((gaussExponent (oneLabel l).1).toNat : Real) *
      paperRootCoefficientFamily (l := l) T b i) *
    arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
      Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
    Set (qVFamTensorBlock T b)))
  exact Submodule.closed_of_finiteDimensional _

/-- Nonzero paper hull equals the j=1 paper qPilot region. -/
theorem paperRootThetaHullNonzero_eq_qPilotPaperRegion :
    paperRootThetaHullNonzero (l := l) T b =
      qPilotPaperRegion (l := l) T b := by
  have hclosed : PaperRootHullNonzeroClosedGap (l := l) T b := by
    unfold PaperRootHullNonzeroClosedGap
    exact rootMinimalRegion_closed (l := l) T b
  have hmin := rootThetaHullNonzero_eq_minimal_of_closed (l := l)
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (cRoot := paperRootCoefficientFamily (l := l) T b)
    (oneLabel := oneLabel l)
    (paperRootCoefficientFamily_nonneg (l := l) T b)
    (SignedLabelOneActual.gaussExponent_oneLabel l) hclosed
  unfold paperRootThetaHullNonzero qPilotPaperRegion rootMinimalRegion at *
  rw [hmin]
  congr 1
  funext i
  rw [SignedLabelOneActual.gaussExponent_oneLabel]
  ring


/-- Paper per-b nonzero theta hull log: the S779/S805 nonzero hull, not the
zero-inclusive old hull. -/
noncomputable def paperPerBThetaHullLogNonzero
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (paperRootThetaHullNonzero (l := l) T b)

/-- The nonzero per-b theta hull log equals the paper least lambda-O hull log. -/
theorem paperPerBThetaHullLogNonzero_eq_paperLeastLambdaOHullLog
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] :
    paperPerBThetaHullLogNonzero (l := l) T b mu =
      paperLeastLambdaOHullLog (l := l) T b mu := by
  unfold paperPerBThetaHullLogNonzero paperLeastLambdaOHullLog
  rw [paperRootThetaHullNonzero_eq_qPilotPaperRegion (l := l) T b]
  rw [paperLeastLambdaOHull_eq_minimal (l := l) T b]
  rfl

/-- The old zero-inclusive hull log is not used; this is the nonzero replacement. -/
def PaperPerBThetaHullLogNonzeroRequired : Prop :=
  paperPerBThetaHullLogNonzero (l := l) T b Measure.addHaar =
    paperLeastLambdaOHullLog (l := l) T b Measure.addHaar

theorem paperPerBThetaHullLogNonzeroRequired_actual :
    PaperPerBThetaHullLogNonzeroRequired (l := l) T b :=
  paperPerBThetaHullLogNonzero_eq_paperLeastLambdaOHullLog (l := l) T b
    Measure.addHaar

end LeanFormal.IUT.XiFPaper.S900PerBThetaHullLogNonzeroActual

end
