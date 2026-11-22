import tmp.sheaf.xif.paper.S929RQpilotPaperSHullFinalActual
import tmp.sheaf.xif.paper.S918RQpilotVolumeLeSHullActual
import tmp.sheaf.xif.paper.S924S918InequalityFixedActual

/-! # S932: actual S918 positivity from S929, and the per-b inequality

S929 identifies s914R with the S922 modelHull and proves its measure is
positive.  This removes the exact S918RPos field: V(R) <= V(S) is actual.
No equality, no spectral/S778 transfer, no scaling data. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S932S918ActualPositivityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open LeanFormal.IUT.XiFPaper.S918RQpilotVolumeLeSHullActual
open LeanFormal.IUT.XiFPaper.S929RQpilotPaperSHullFinalActual
open LeanFormal.IUT.XiFPaper.S924S918InequalityFixedActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]

/-- Actual positivity of the paper-order R measure, from S929. -/
theorem s914R_measure_pos_actual :
    S918RMeasurePosRequired (l := l) T b mu :=
  S929RQpilotPaperSHullFinalActual.S918RMeasurePosRequired_actual
    (l := l) T b mu

/-- S918/S924 per-b inequality V(R) <= V(S), unconditional. -/
theorem s932V_R_le_V_S :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (s914R (l := l) T b) ≤
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (s914S (l := l) T b) :=
  s918V_R_le_V_S (l := l) T b mu (s914R_measure_pos_actual (l := l) T b mu)

/-- Inequality-only package: containment, positivity, finiteness, V(R)<=V(S). -/
theorem s932InequalityPackage :
    s914R (l := l) T b ⊆ s914S (l := l) T b ∧
      0 < mu (s914R (l := l) T b) ∧
      mu (s914S (l := l) T b) < ⊤ ∧
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
          (s914R (l := l) T b) ≤
        arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
          (s914S (l := l) T b) :=
  ⟨s914R_subset_S (l := l) T b,
    s914R_measure_pos_actual (l := l) T b mu,
    s918S_measure_lt_top (l := l) T b mu,
    s932V_R_le_V_S (l := l) T b mu⟩

end LeanFormal.IUT.XiFPaper.S932S918ActualPositivityActual
end
