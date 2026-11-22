import tmp.sheaf.xif.paper.S973QPilotTensorImagePositivityActual
import tmp.sheaf.xif.paper.S976FiniteLogShellHaarActual
import tmp.sheaf.xif.paper.S981TensorRegionHullFiniteActual

-- S990: finite-carrier closedBall/unitRegion actual positivity and
-- finiteness; paper-side qPilot positivity and hull finiteness under
-- exact minimal inputs (no fake transport).

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S990FiniteCarrierPositivityFinitenessActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S970FiniteLogShellCarrierActual
open LeanFormal.IUT.XiFPaper.S976FiniteLogShellHaarActual
open LeanFormal.IUT.XiFPaper.S973QPilotTensorImagePositivityActual
open LeanFormal.IUT.XiFPaper.S981TensorRegionHullFiniteActual
open LeanFormal.IUT.XiFPaper.S962TensorPacketPaperInequalityActual
open LeanFormal.IUT.XiFPaper.S971TensorRegionImageActual
open LeanFormal.IUT.XiFPaper.S979TensorRegionHullInequalityActual
open MeasureTheory

universe u

variable {p : Nat} [Fact p.Prime]

/-- Finite log-shell unit region (closedBall). -/
noncomputable def finiteCarrierUnitRegion (d : Nat) :
    Set (FiniteLogShellCarrier p d) :=
  (finiteLogShellHaarData (p := p) d).unitRegion

theorem finiteCarrierUnitRegion_pos (d : Nat) :
    0 < (finiteLogShellHaarData (p := p) d).measure
      (finiteCarrierUnitRegion (p := p) d) :=
  (finiteLogShellHaarData (p := p) d).unit_pos

theorem finiteCarrierUnitRegion_lt_top (d : Nat) :
    (finiteLogShellHaarData (p := p) d).measure
      (finiteCarrierUnitRegion (p := p) d) < ⊤ :=
  (finiteLogShellHaarData (p := p) d).unit_lt_top

/-- Any set containing the finite unit region has positive measure. -/
theorem finiteCarrier_measure_pos_of_unitRegion_subset (d : Nat)
    (S : Set (FiniteLogShellCarrier p d))
    (h : finiteCarrierUnitRegion (p := p) d ⊆ S) :
    0 < (finiteLogShellHaarData (p := p) d).measure S :=
  lt_of_lt_of_le (finiteCarrierUnitRegion_pos (p := p) d) (measure_mono h)

/-- Any set contained in the finite unit region has finite measure. -/
theorem finiteCarrier_measure_lt_top_of_subset_unitRegion (d : Nat)
    (S : Set (FiniteLogShellCarrier p d))
    (h : S ⊆ finiteCarrierUnitRegion (p := p) d) :
    (finiteLogShellHaarData (p := p) d).measure S < ⊤ :=
  lt_of_le_of_lt (measure_mono h) (finiteCarrierUnitRegion_lt_top (p := p) d)

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (D : FinalLTensorLogVolumeData (l := l) T b)

/-- Exact positivity input on the paper carrier. -/
def S990QPilotImagePositivityInput : Prop :=
  S973DQPilotImageInteriorNonempty (l := l) T b D

/-- Exact finiteness input: paper hull inside finite unitRegion. -/
def S990HullFinitenessInput : Prop :=
  S981TensorRegionHullSubsetUnitRegion (l := l) T b D

def S990PaperInputs : Prop :=
  S990QPilotImagePositivityInput (l := l) T b D ∧
    S990HullFinitenessInput (l := l) T b D

theorem s990QPilotImage_measure_pos
    (h : S990QPilotImagePositivityInput (l := l) T b D) :
    0 < D.measure (qPilotPaperImageInLValued (l := l) T b) := by
  letI := D.topologicalSpace
  letI := D.measurableSpace
  letI := D.borelSpace
  letI := D.isTopologicalAddGroup
  letI := D.locallyCompactSpace
  letI := D.isAddHaar
  exact s973DQPilotImage_measure_pos_of_interior (l := l) T b D h

theorem s990TensorRegionHull_measure_lt_top
    (h : S990HullFinitenessInput (l := l) T b D) :
    D.measure (tensorRegionHull T b D) < ⊤ :=
  tensorRegionHull_measure_lt_top_of_subset T b D h

theorem s990PerBInequality
    (h : S990PaperInputs (l := l) T b D) :
    qPilotTensorLog T b D ≤
      tensorRegionHullLog T b D := by
  obtain ⟨hpos, hfin⟩ := h
  exact qPilotTensorLog_le_tensorRegionHullLog T b D
    (s990QPilotImage_measure_pos T b D hpos)
    (s990TensorRegionHull_measure_lt_top T b D hfin)

#check finiteCarrier_measure_pos_of_unitRegion_subset
#check finiteCarrier_measure_lt_top_of_subset_unitRegion
#check s990QPilotImage_measure_pos
#check s990TensorRegionHull_measure_lt_top
#check s990PerBInequality

end LeanFormal.IUT.XiFPaper.S990FiniteCarrierPositivityFinitenessActual

end