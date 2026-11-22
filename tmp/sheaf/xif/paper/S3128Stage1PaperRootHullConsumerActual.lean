import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
noncomputable section
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators
open LeanFormal.IUT
open MeasureTheory
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1PaperRootHullConsumerActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Consumer: paper-hull gap gives the local hull log formula. -/
theorem S3128Stage1PaperRootHullLog_eq_formula
    (b : Bad (nativePlaceSelection T)) (mu : Measure (qVFamTensorBlock T b))
    [Measure.IsAddHaarMeasure mu] (G : PaperRootHullFormulaGap T b) :
    paperRootThetaHullLog T b mu = paperRootThetaFormulaLog T b :=
  paperRootThetaHullLog_eq_formula_of_gap T b mu G

/-- Consumer: gaps at every bad place give the global hull scalar formula. -/
theorem S3128Stage1PaperRootHullScalar_eq_formula
    (G : ∀ b : Bad (nativePlaceSelection T), PaperRootHullFormulaGap T b) :
    paperRootThetaHullScalar T = paperRootThetaFormulaScalar T :=
  paperRootThetaHullScalar_eq_formula_of_gap T G

#check S3128Stage1PaperRootHullLog_eq_formula
#check S3128Stage1PaperRootHullScalar_eq_formula
end LeanFormal.IUT.XiFPaper.S3128Stage1PaperRootHullConsumerActual