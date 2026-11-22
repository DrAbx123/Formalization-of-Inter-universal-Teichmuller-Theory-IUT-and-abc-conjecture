import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.SignedLabelOneActual

/-! # S806: nonzero paper root hull closedness and formula gaps

PaperRootHullNonzeroClosedGap := IsClosed of the minimal region
  F(paperRootCoefficientFamily)*O_hol.
PaperRootHullNonzeroFormulaBridge := nonzero hull log = -sum c log p.
The closedness follows from compactness of the minimal region.
The formula follows from the hull/minimal equality plus the actual fractional
scaling data.  No closedness, equality or formula is fabricated. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S806PaperRootHullNonzeroGapsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem paperRootCoefficientFamily_nonneg (i : qVFamTensorV) :
    0 <= paperRootCoefficientFamily (l := l) T b i := by
  unfold paperRootCoefficientFamily qVFamPaperRootCoefficient
  positivity

/-- Minimal paper root region F(c_root)*O_hol. -/
noncomputable def paperRootMinimalRegion : Set (qVFamTensorBlock T b) :=
  rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
    (paperRootCoefficientFamily (l := l) T b) (oneLabel l)

/-- Nonzero paper root closure hull (all nonzero signed labels). -/
noncomputable def paperRootThetaHullNonzero : Set (qVFamTensorBlock T b) :=
  closure (⋃ j : {j : SignedLabel l.value // j.1 ≠ 0},
    rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily (l := l) T b) j.1)

/-- Exact closedness gap of the minimal paper region. -/
def PaperRootHullNonzeroClosedGap : Prop :=
  IsClosed (paperRootMinimalRegion (l := l) T b)

/-- Compactness supplies the closedness gap. -/
theorem paperRootHullNonzeroClosedGap_of_compact
    (hcompact : IsCompact (paperRootMinimalRegion (l := l) T b)) :
    PaperRootHullNonzeroClosedGap (l := l) T b :=
  hcompact.isClosed

/-- Exact hull/minimal equality needed for the formula. -/
def PaperRootHullNonzeroHullEquality : Prop :=
  paperRootThetaHullNonzero (l := l) T b = paperRootMinimalRegion (l := l) T b

/-- Nonzero paper root hull log. -/
noncomputable def paperRootThetaHullLogNonzero : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
    Measure.addHaar (paperRootThetaHullNonzero (l := l) T b)

/-- Exact formula bridge. -/
def PaperRootHullNonzeroFormulaBridge : Prop :=
  paperRootThetaHullLogNonzero (l := l) T b =
    -((∑ _ : qVFamTensorV, paperRootCoefficientFamily (l := l) T b ()) *
      Real.log (qVFamTensorP T b : Real))

/-- Conditional formula bridge from hull equality plus actual scaling data. -/
theorem paperRootHullNonzeroFormulaBridge_of_equality_and_data
    (heq : PaperRootHullNonzeroHullEquality (l := l) T b)
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily (l := l) T b)) :
    PaperRootHullNonzeroFormulaBridge (l := l) T b := by
  unfold PaperRootHullNonzeroFormulaBridge paperRootThetaHullLogNonzero
  rw [heq]
  unfold paperRootMinimalRegion rootThetaRegion
  have hsimple : (fun i : qVFamTensorV =>
      ((gaussExponent (oneLabel l).1).toNat : Real) *
        paperRootCoefficientFamily (l := l) T b i) =
      paperRootCoefficientFamily (l := l) T b := by
    funext i
    rw [gaussExponent_oneLabel l]
    norm_num
  rw [hsimple]
  exact arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (qVFamTensorPlaces T b) qVFamTensorTuple Measure.addHaar data

end LeanFormal.IUT.XiFPaper.S806PaperRootHullNonzeroGapsActual

end
