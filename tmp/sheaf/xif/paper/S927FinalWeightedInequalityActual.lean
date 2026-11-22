import tmp.sheaf.xif.paper.S924S918InequalityFixedActual
import tmp.sheaf.xif.paper.S919GlobalWeightedInequalityActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S927FinalWeightedInequalityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open LeanFormal.IUT.XiFPaper.S921RQpilotPaperRegionPositivityActual
open LeanFormal.IUT.XiFPaper.S924S918InequalityFixedActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-- Per-b V(R_b), the qPilot paper region log. -/
noncomputable def perBVRGlobal (b : Bad (nativePlaceSelection T)) : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
    (mu b) (s914R (l := l) T b)

/-- Per-b V(S_b), the nonzero theta hull log. -/
noncomputable def perBVSGlobal (b : Bad (nativePlaceSelection T)) : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
    (mu b) (s914S (l := l) T b)

/-- Final weighted paper inequality: sum_b w_b V(R_b) <= sum_b w_b V(S_b). -/
def paperWeightedInequality : Prop :=
  weightedPaperV (l := l) T (perBVRGlobal (l := l) T mu) ≤
    weightedPaperV (l := l) T (perBVSGlobal (l := l) T mu)

/-- Conditional final assembly: interior of every R_b and finiteness of every
S_b imply the weighted paper inequality.  No equality/scaling data. -/
theorem paperWeightedInequality_of_interior_finite
    (hint : ∀ b : Bad (nativePlaceSelection T),
      S921RInteriorNonempty (l := l) T b)
    (hfin : ∀ b : Bad (nativePlaceSelection T),
      mu b (s914S (l := l) T b) < ⊤) :
    paperWeightedInequality (l := l) T mu := by
  unfold paperWeightedInequality
  apply weightedPaperV_mono (l := l) T
  intro b
  exact s924V_R_le_V_S_of_interior_finite (l := l) T b (mu b) (hint b) (hfin b)

/-- Exact conditional hypothesis package. -/
def S927InteriorFinitenessHypotheses : Prop :=
  (∀ b : Bad (nativePlaceSelection T), S921RInteriorNonempty (l := l) T b) ∧
    (∀ b : Bad (nativePlaceSelection T),
      mu b (s914S (l := l) T b) < ⊤)

theorem paperWeightedInequality_of_package
    (h : S927InteriorFinitenessHypotheses (l := l) T mu) :
    paperWeightedInequality (l := l) T mu :=
  paperWeightedInequality_of_interior_finite (l := l) T mu h.1 h.2

end LeanFormal.IUT.XiFPaper.S927FinalWeightedInequalityActual

end
