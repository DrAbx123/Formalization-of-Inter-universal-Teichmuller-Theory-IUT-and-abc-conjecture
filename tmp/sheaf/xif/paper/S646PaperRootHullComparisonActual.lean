import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual
import tmp.sheaf.xif.paper.SignedLabelOneActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual

-- S646: use existing root-hull objects.  Exact formula equality remains
-- PaperRootHullFormulaGap; the actual qPilot comparison is the containment
-- inequality qPilotClassicalLog <= root theta hull log.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S646PaperRootHullComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open MeasureTheory
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact missing pointwise correction comparison: paper order/(2l) vs c_norm. -/
def PaperRootCoefficientLeRootNorm : Prop :=
  ∀ i : qVFamTensorV,
    paperRootCoefficientFamily T b i ≤ rootNormCoefficient (l := l) T b i
/-- Actual qPilot/root-hull comparison, conditional only on Haar positivity
and finiteness of the root hull. -/
theorem qPilotClassicalLog_le_paperRootHullLog
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]
    (hge : PaperRootCoefficientLeRootNorm (l := l) T b)
    (hpos : 0 < mu (qPilotClassicalRegion (qVFamTensorPlaces T b)
      qVFamTensorTuple (rootNormCoefficient (l := l) T b)))
    (hfin : mu (paperRootThetaHull T b) < ⊤) :
    qPilotClassicalLog (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (rootNormCoefficient (l := l) T b)
        (rootNormScalingData (l := l) T b) ≤
      paperRootThetaHullLog T b mu := by
  have h := qPilotClassicalLog_le_rootThetaHullLog (l := l)
    (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (rootNormCoefficient (l := l) T b)
    (paperRootCoefficientFamily T b)
    (rootNormScalingData (l := l) T b)
    hge
    (oneLabel (l := l)) (gaussExponent_oneLabel (l := l)) hpos
    (by simpa [paperRootThetaHull, rootThetaHull] using hfin)
  simpa [paperRootThetaHullLog, rootThetaHullLog, paperRootCoefficientFamily] using h

def PaperRootHullFormulaGapRequired : Prop :=
  Nonempty (PaperRootHullFormulaGap T b)

theorem paperRootHullFormula_from_gap
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]
    (G : PaperRootHullFormulaGap T b) :
    paperRootThetaHullLog T b mu = paperRootThetaFormulaLog T b :=
  paperRootThetaHullLog_eq_formula_of_gap T b mu G

#check qPilotClassicalLog_le_paperRootHullLog
#check PaperRootCoefficientLeRootNorm
#check PaperRootHullFormulaGapRequired
#check paperRootHullFormula_from_gap

end LeanFormal.IUT.XiFPaper.S646PaperRootHullComparisonActual

end