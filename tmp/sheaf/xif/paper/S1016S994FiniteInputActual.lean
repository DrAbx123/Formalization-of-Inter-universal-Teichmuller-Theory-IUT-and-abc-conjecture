import tmp.sheaf.xif.paper.S994FiniteCarrierCor312Actual
import tmp.sheaf.xif.paper.S1007QPilotPositivityActual
import tmp.sheaf.xif.paper.S1008S1004HullFiniteActual

-- S1016: construct S994FiniteInput from S1008 actual hull finiteness and
-- S1007 positivity (conditional on F(cRoot) open), or exact positivity.

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 20000000

namespace LeanFormal.IUT.XiFPaper.S1016S994FiniteInputActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1004QVFamFiniteLinearizationActual
open LeanFormal.IUT.XiFPaper.S1007QPilotPositivityActual
open LeanFormal.IUT.XiFPaper.S1008S1004HullFiniteActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S923RInteriorNonemptyActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Realignment: the S994 actual linearization is the S1004 linearization. -/
theorem s1016H_eq :
    s994H (l := l) T b (s994ActualLinearization (l := l) T b) =
      s1004H (l := l) T b := rfl

theorem s1016QPilotImage_eq :
    s994QPilotImage (l := l) T b (s994ActualLinearization (l := l) T b) =
      s1004QPilotImage (l := l) T b := rfl

theorem s1016Hull_eq :
    s994Hull (l := l) T b (s994ActualLinearization (l := l) T b) =
      s1004Hull (l := l) T b := rfl

/-- Exact positivity input for the S994 finite input. -/
def S1016QPilotPositivityInput : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    0 < (s994H (l := l) T b (s994ActualLinearization (l := l) T b)).measure
      (s994QPilotImage (l := l) T b (s994ActualLinearization (l := l) T b))

/-- Construct S994FiniteInput from exact positivity; hull finiteness is actual. -/
noncomputable def s994FiniteInput_of_positivity
    (hpos : S1016QPilotPositivityInput (l := l) T) :
    S994FiniteInput T where
  L := fun b => s994ActualLinearization (l := l) T b
  qPilot_pos := hpos
  hull_finite := fun b => by
    rw [s1016Hull_eq (l := l) T b]
    exact s1008Hull_measure_lt_top (l := l) T b

/-- Construct S994FiniteInput from F(cRoot) openness (S1007 positivity). -/
noncomputable def s994FiniteInput_of_fractionalOpen
    (hopen : ∀ b : Bad (nativePlaceSelection T),
      S923FractionalLatticeOpen (l := l) T b) :
    S994FiniteInput T :=
  s994FiniteInput_of_positivity (l := l) T (fun b => by
    rw [s1016H_eq (l := l) T b, s1016QPilotImage_eq (l := l) T b]
    exact s1007QPilotImage_measure_pos_of_open (l := l) T b (hopen b))

#check s994FiniteInput_of_positivity
#check s994FiniteInput_of_fractionalOpen
#check S1016QPilotPositivityInput

end LeanFormal.IUT.XiFPaper.S1016S994FiniteInputActual

end