import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S719PaperRootHullGapDecompositionActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

structure PaperRootHullScalingDataGap (b : Bad (nativePlaceSelection T)) where
  data : ArithmeticTuplePureFractionalScalingData
    (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b)

def PaperRootHullSetGap (b : Bad (nativePlaceSelection T)) : Prop :=
  paperRootThetaHull T b =
    ((arithmeticTupleFractionalLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b) *
      arithmeticTupleHolomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple :
        Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
      Set (qVFamTensorBlock T b))

theorem paperRootHullFormulaGap_iff_parts (b : Bad (nativePlaceSelection T)) :
    PaperRootHullFormulaGap T b ↔
      Nonempty (PaperRootHullScalingDataGap T b) ∧ PaperRootHullSetGap T b := by
  constructor
  · intro G
    exact ⟨⟨G.data⟩, G.hull_eq⟩
  · rintro ⟨⟨data⟩, hhull⟩
    exact ⟨data, hhull⟩

theorem paperRootThetaHull_eq_union (b : Bad (nativePlaceSelection T)) :
    paperRootThetaHull T b =
      closure (⋃ j : SignedLabel l.value,
        rootThetaRegion (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
          (paperRootCoefficientFamily T b) j) := rfl

theorem paperRootThetaHullLog_eq_formula_of_parts
    (b : Bad (nativePlaceSelection T))
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]
    (data : PaperRootHullScalingDataGap T b) (hhull : PaperRootHullSetGap T b) :
    paperRootThetaHullLog T b mu = paperRootThetaFormulaLog T b :=
  paperRootThetaHullLog_eq_formula_of_gap T b mu ⟨data.data, hhull⟩

end LeanFormal.IUT.XiFPaper.S719PaperRootHullGapDecompositionActual
end