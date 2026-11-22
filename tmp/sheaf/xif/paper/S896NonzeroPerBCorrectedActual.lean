import tmp.sheaf.xif.paper.S779RootHullNonzeroFixActual
import tmp.sheaf.xif.paper.S805NonzeroHullReplacementActual
import tmp.sheaf.xif.paper.S822PadicDetHullActual
import tmp.sheaf.xif.paper.S154PaperNormalizedQUnitActual

/-! # S896: per-b corrected 2l on the nonzero paper hull

Exact minimal inputs: (i) closedness of the j=1 minimal region; (ii) actual
fractional scaling data at the paper coefficient order/(2l).  Given these,
the nonzero hull equals the j=1 paper qPilot region, its log is the paper
formula, and 2l times it is exactly perBQPilotLog (c_norm = order). -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S896NonzeroPerBCorrectedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S822PadicDetHullActual
open LeanFormal.IUT.XiFPaper.S154PaperNormalizedQUnitActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact closedness input at b. -/
def ClosedInput (b : Bad (nativePlaceSelection T)) : Prop :=
  PaperRootHullNonzeroClosedGap (l := l) T b

theorem paperRootThetaHullNonzero_eq_qPilotPaperRegion
    (hclosed : ClosedInput (l := l) T b) :
    paperRootThetaHullNonzero (l := l) T b =
      qPilotPaperRegion (l := l) T b := by
  have hmin := rootThetaHullNonzero_eq_minimal_of_closed (l := l)
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (cRoot := paperRootCoefficientFamily (l := l) T b)
    (oneLabel := oneLabel l)
    (paperRootCoefficientFamily_nonneg (l := l) T b)
    (gaussExponent_oneLabel l) hclosed
  unfold paperRootThetaHullNonzero qPilotPaperRegion rootMinimalRegion at *
  rw [hmin]
  congr 1
  funext i
  rw [gaussExponent_oneLabel]
  ring

/-- Nonzero paper hull log equals the paper formula, given closedness and
actual scaling data at the paper coefficient. -/
theorem paperRootThetaHullLogNonzero_eq_formula
    (hclosed : ClosedInput (l := l) T b)
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily (l := l) T b)) :
    paperRootThetaHullLogNonzero (l := l) T b Measure.addHaar =
      -((∑ _ : qVFamTensorV, paperRootCoefficientFamily (l := l) T b ()) *
        Real.log (qVFamTensorP T b : Real)) := by
  unfold paperRootThetaHullLogNonzero
  rw [paperRootThetaHullNonzero_eq_qPilotPaperRegion (l := l) T b hclosed]
  unfold qPilotPaperRegion thetaTensorScaledRegion paperLambdaORegion
  exact normalizedLogVolume_lambdaOSet (l := l) T b Measure.addHaar data

/-- Per-b corrected 2l on the nonzero paper hull. -/
def perBCorrectedNonzero : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    perBQPilotLog (l := l) T b ≤
      (2 * (l.value : Real)) *
        paperRootThetaHullLogNonzero (l := l) T b Measure.addHaar

/-- Actual per-b corrected 2l, conditional only on closedness and paper data. -/
theorem perBCorrectedNonzero_of_closed_data
    (hclosed : ∀ b : Bad (nativePlaceSelection T), ClosedInput (l := l) T b)
    (data : ∀ b : Bad (nativePlaceSelection T),
      ArithmeticTuplePureFractionalScalingData
        (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily (l := l) T b)) :
    perBCorrectedNonzero (l := l) T := by
  intro b
  rw [paperRootThetaHullLogNonzero_eq_formula (l := l) T b (hclosed b) (data b)]
  rw [perBQPilotLog_eq_neg_cNorm_mul_logp (l := l) T b]
  rw [qVFamNormalizedCoefficient_eq_order (l := l) T b]
  exact le_of_eq (hullLogFunctional_twoL_mul (l := l) T b).symm

/-- Exact minimal input: closedness plus paper-coefficient scaling data. -/
def NonzeroPerBExactInput : Prop :=
  (∀ b : Bad (nativePlaceSelection T), ClosedInput (l := l) T b) ∧
    (∀ b : Bad (nativePlaceSelection T),
      Nonempty (ArithmeticTuplePureFractionalScalingData
        (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily (l := l) T b)))

end LeanFormal.IUT.XiFPaper.S896NonzeroPerBCorrectedActual
end
