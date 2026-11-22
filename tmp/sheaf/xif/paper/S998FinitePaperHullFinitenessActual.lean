import tmp.sheaf.xif.paper.S994FiniteCarrierCor312Actual
import tmp.sheaf.xif.paper.S978FiniteCarrierHullActual
import tmp.sheaf.xif.paper.S990FiniteCarrierPositivityFinitenessActual

-- S998: finitePaperHull finiteness from hull ⊆ finite unitRegion.
-- Exact geometric condition or exact finite-measure field.

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S998FinitePaperHullFinitenessActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S970FiniteLogShellCarrierActual
open LeanFormal.IUT.XiFPaper.S976FiniteLogShellHaarActual
open LeanFormal.IUT.XiFPaper.S989FiniteCarrierDirectActual
open LeanFormal.IUT.XiFPaper.S978FiniteCarrierHullActual
open LeanFormal.IUT.XiFPaper.S990FiniteCarrierPositivityFinitenessActual
open LeanFormal.IUT.XiFPaper.S965FinalLCarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open MeasureTheory Topology

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (L : S965CarrierLinearization (l := l) T b)

/-- Exact geometric input: finitePaperHull inside the finite unitRegion. -/
def S998FiniteHullSubsetUnitRegion : Prop :=
  finitePaperHull (l := l) T b L ⊆
    (finitePaperTensorData (l := l) T b L.d).unitRegion

theorem finitePaperHull_measure_lt_top_of_subset
    (h : S998FiniteHullSubsetUnitRegion (l := l) T b L) :
    (finitePaperTensorData (l := l) T b L.d).measure
      (finitePaperHull (l := l) T b L) < ⊤ := by
  exact lt_of_le_of_lt (measure_mono h) (finitePaperTensorData (l := l) T b L.d).unit_lt_top

/-- Exact minimal finite-measure field. -/
def S998FiniteHullMeasure : Prop :=
  (finitePaperTensorData (l := l) T b L.d).measure
    (finitePaperHull (l := l) T b L) < ⊤

theorem finitePaperHull_measure_lt_top_of_exact
    (h : S998FiniteHullMeasure (l := l) T b L) :
    (finitePaperTensorData (l := l) T b L.d).measure
      (finitePaperHull (l := l) T b L) < ⊤ :=
  h

/-- Fill S994FiniteInput's hull_finite field under the geometric subset. -/
noncomputable def s994FiniteInput_of_hull_subset
    (L : (b : Bad (nativePlaceSelection T)) → S965CarrierLinearization (l := l) T b)
    (hpos : ∀ b : Bad (nativePlaceSelection T),
      0 < (finitePaperTensorData (l := l) T b (L b).d).measure
        (finiteQPilotImage (l := l) T b (L b)))
    (hsub : ∀ b : Bad (nativePlaceSelection T),
      S998FiniteHullSubsetUnitRegion (l := l) T b (L b)) :
    S994FiniteInput T where
  L := L
  qPilot_pos := hpos
  hull_finite := fun b =>
    finitePaperHull_measure_lt_top_of_subset (l := l) T b (L b) (hsub b)

/-- Fill S994FiniteInput's hull_finite field under exact finite measure. -/
noncomputable def s994FiniteInput_of_hull_measure
    (L : (b : Bad (nativePlaceSelection T)) → S965CarrierLinearization (l := l) T b)
    (hpos : ∀ b : Bad (nativePlaceSelection T),
      0 < (finitePaperTensorData (l := l) T b (L b).d).measure
        (finiteQPilotImage (l := l) T b (L b)))
    (hfin : ∀ b : Bad (nativePlaceSelection T),
      S998FiniteHullMeasure (l := l) T b (L b)) :
    S994FiniteInput T where
  L := L
  qPilot_pos := hpos
  hull_finite := fun b => hfin b

#check finitePaperHull_measure_lt_top_of_subset
#check s994FiniteInput_of_hull_subset
#check S998FiniteHullMeasure

end LeanFormal.IUT.XiFPaper.S998FinitePaperHullFinitenessActual

end