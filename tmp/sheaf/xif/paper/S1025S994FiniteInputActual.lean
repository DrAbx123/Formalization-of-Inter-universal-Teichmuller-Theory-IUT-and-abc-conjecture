import tmp.sheaf.xif.paper.S1016S994FiniteInputActual
import tmp.sheaf.xif.paper.S1023FractionalLatticeOpenActual

-- S1025: actual Nonempty S994FiniteInput, using S1023 actual openness
-- of F(cRoot) and S1008 actual hull finiteness.

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 20000000

namespace LeanFormal.IUT.XiFPaper.S1025S994FiniteInputActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1016S994FiniteInputActual
open LeanFormal.IUT.XiFPaper.S1023FractionalLatticeOpenActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S923RInteriorNonemptyActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Actual S994FiniteInput: actual linearization, actual qPilot positivity
from S1023/S1007, actual hull finiteness from S1008. -/
noncomputable def s994FiniteInput_actual : S994FiniteInput T :=
  s994FiniteInput_of_fractionalOpen (l := l) T
    (fun b => s923FractionalLatticeOpen_actual (l := l) T b)

theorem nonempty_s994FiniteInput : Nonempty (S994FiniteInput T) :=
  ⟨s994FiniteInput_actual (l := l) T⟩

/-- Actual positivity fields, using S1023 actual openness. -/
theorem s1025QPilotPositivityInput_actual :
    S1016QPilotPositivityInput (l := l) T :=
  (s994FiniteInput_actual (l := l) T).qPilot_pos

#check s994FiniteInput_actual
#check nonempty_s994FiniteInput
#check s1025QPilotPositivityInput_actual

end LeanFormal.IUT.XiFPaper.S1025S994FiniteInputActual

end