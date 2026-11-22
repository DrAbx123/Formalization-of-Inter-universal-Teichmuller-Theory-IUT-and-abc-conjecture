import tmp.sheaf.xif.paper.S973QPilotTensorImagePositivityActual
import tmp.sheaf.xif.paper.S976FiniteLogShellHaarActual
import tmp.sheaf.xif.paper.S923RInteriorNonemptyActual
/-! # S980: qPilot/Tensor image positivity
On the qVFam block, openness of the fractional lattice F(cRoot) gives
0 in interior(qPilotPaperRegion) and hence positive addHaar (actual conditional
from S923).  On the finite log-shell carrier, S976 supplies actual Haar and
positive finite unit ball.  For the L-valued tensor image, the exact remaining
input is nonempty interior on the S956/S973 carrier; no fake embedding/measure
transport is asserted. -/
noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S980QPilotImagePositivityActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open LeanFormal.IUT.XiFPaper.S921RQpilotPaperRegionPositivityActual
open LeanFormal.IUT.XiFPaper.S923RInteriorNonemptyActual
open LeanFormal.IUT.XiFPaper.S973QPilotTensorImagePositivityActual
open LeanFormal.IUT.XiFPaper.S976FiniteLogShellHaarActual
open LeanFormal.IUT.XiFPaper.S970FiniteLogShellCarrierActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
/-- qVFam-side actual positivity from openness of F(cRoot). -/
theorem s980QPilotRegion_measure_pos_of_open
    (hopen : S923FractionalLatticeOpen (l := l) T b) :
    0 < MeasureTheory.Measure.addHaar (s914R (l := l) T b) :=
  s923R_measure_pos_of_open (l := l) T b hopen
/-- Finite log-shell carrier actual positive finite unit mass (S976). -/
theorem s980FiniteLogShell_unit_pos (p d : Nat) [Fact p.Prime] :
    0 < (finiteLogShellHaarData (p := p) d).measure
      (finiteLogShellHaarData (p := p) d).unitRegion :=
  (finiteLogShellHaarData (p := p) d).unit_pos
theorem s980FiniteLogShell_unit_lt_top (p d : Nat) [Fact p.Prime] :
    (finiteLogShellHaarData (p := p) d).measure
      (finiteLogShellHaarData (p := p) d).unitRegion < ⊤ :=
  (finiteLogShellHaarData (p := p) d).unit_lt_top
/-- Exact remaining S979 positivity input on the L-valued carrier. -/
def S980FinalLImageInteriorExactInput
    (D : FinalLTensorLogVolumeData (l := l) T b) : Prop :=
  S973DQPilotImageInteriorNonempty (l := l) T b D
/-- Exact input gives D-measure positivity, actual. -/
theorem s980FinalLImage_measure_pos
    (D : FinalLTensorLogVolumeData (l := l) T b)
    (h : S980FinalLImageInteriorExactInput (l := l) T b D) :
    0 < D.measure (qPilotPaperImageInLValued (l := l) T b) := by
  letI := D.topologicalSpace
  letI := D.measurableSpace
  letI := D.borelSpace
  letI := D.isTopologicalAddGroup
  letI := D.locallyCompactSpace
  letI := D.isAddHaar
  exact s973DQPilotImage_measure_pos_of_interior (l := l) T b D h
end LeanFormal.IUT.XiFPaper.S980QPilotImagePositivityActual
