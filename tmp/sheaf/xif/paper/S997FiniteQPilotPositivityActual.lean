import tmp.sheaf.xif.paper.S994FiniteCarrierCor312Actual
import tmp.sheaf.xif.paper.S990FiniteCarrierPositivityFinitenessActual
import tmp.sheaf.xif.paper.S989FiniteCarrierDirectActual
import tmp.sheaf.xif.paper.S973QPilotTensorImagePositivityActual

/-! # S997: qPilot positivity on the finite carrier

S990 gives positivity from finiteCarrierUnitRegion ⊆ S.  For the finite
qPilot image this inclusion is the exact geometric input; given it,
S994PerBInput.qPilot_pos is actual.  The nonempty-interior form is recorded
as the equivalent exact alternative. -/

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S997FiniteQPilotPositivityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S970FiniteLogShellCarrierActual
open LeanFormal.IUT.XiFPaper.S976FiniteLogShellHaarActual
open LeanFormal.IUT.XiFPaper.S965FinalLCarrierTopologyActual
open LeanFormal.IUT.XiFPaper.S989FiniteCarrierDirectActual
open LeanFormal.IUT.XiFPaper.S990FiniteCarrierPositivityFinitenessActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S973QPilotTensorImagePositivityActual
open MeasureTheory Topology

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact positivity input: the finite unit region is contained in the qPilot image. -/
def S997UnitRegionSubsetQPilot
    (L : S965CarrierLinearization (l := l) T b) : Prop :=
  finiteCarrierUnitRegion (p := qVFamTensorP T b) L.d ⊆
    finiteQPilotImage (l := l) T b L

/-- Actual positivity of the finite qPilot image from unit-region containment. -/
theorem s997QPilotImage_measure_pos_of_unitRegion_subset
    (L : S965CarrierLinearization (l := l) T b)
    (h : S997UnitRegionSubsetQPilot (l := l) T b L) :
    0 < (finitePaperTensorData (l := l) T b L.d).measure
      (finiteQPilotImage (l := l) T b L) :=
  finiteCarrier_measure_pos_of_unitRegion_subset
    (p := qVFamTensorP T b) L.d (finiteQPilotImage (l := l) T b L) h

/-- Exact alternative: nonempty interior of the finite qPilot image. -/
def S997QPilotImageInteriorNonempty
    (L : S965CarrierLinearization (l := l) T b) : Prop :=
  (interior (finiteQPilotImage (l := l) T b L)).Nonempty

/-- S994PerBInput with actual qPilot positivity and exact hull finiteness. -/
noncomputable def s994PerBInputOfUnitRegionSubset
    (L : S965CarrierLinearization (l := l) T b)
    (hsubset : S997UnitRegionSubsetQPilot (l := l) T b L)
    (hfinite : (finitePaperTensorData (l := l) T b L.d).measure
      (finitePaperHull (l := l) T b L) < ⊤) :
    S994PerBInput (l := l) T b where
  linearization := L
  qPilot_pos := s997QPilotImage_measure_pos_of_unitRegion_subset
    (l := l) T b L hsubset
  hull_finite := hfinite

/-- Exact minimal per-b positivity field. -/
def S997QPilotPositivityRequired
    (L : S965CarrierLinearization (l := l) T b) : Prop :=
  0 < (finitePaperTensorData (l := l) T b L.d).measure
    (finiteQPilotImage (l := l) T b L)

end LeanFormal.IUT.XiFPaper.S997FiniteQPilotPositivityActual
end
