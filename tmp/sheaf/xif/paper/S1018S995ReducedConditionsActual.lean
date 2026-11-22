import tmp.sheaf.xif.paper.S995FiniteCarrierCor312ConclusionActual
import tmp.sheaf.xif.paper.S1008S1004HullFiniteActual
import tmp.sheaf.xif.paper.S1007QPilotPositivityActual
import tmp.sheaf.xif.paper.S1023FractionalLatticeOpenActual

/-! # S1018: reduced exact conditions for the final S995 input

S1008 proves actual finiteness of the S1004/S994 finite hull, and S1007
reduces positivity to openness of the fractional lattice F(cRoot).  Therefore
the S994FiniteInput positivity/finiteness pair reduces to the single per-b
openness condition.  This file constructs the S994FiniteInput from that
condition, so the final exact list no longer contains hull_finite separately. -/

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1018S995ReducedConditionsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S995FiniteCarrierCor312ConclusionActual
open LeanFormal.IUT.XiFPaper.S1004QVFamFiniteLinearizationActual
open LeanFormal.IUT.XiFPaper.S1007QPilotPositivityActual
open LeanFormal.IUT.XiFPaper.S1008S1004HullFiniteActual
open LeanFormal.IUT.XiFPaper.S923RInteriorNonemptyActual
open LeanFormal.IUT.XiFPaper.S1023FractionalLatticeOpenActual
open MeasureTheory Topology

universe u ua uv upi umon ui uL uC uG uX uLabel uC3 uD3 uM uP
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- The single reduced exact condition: for every bad place the fractional
lattice F(cRoot) is open. -/
def S1018OpennessInput : Prop :=
  ∀ b : Bad (nativePlaceSelection T), S923FractionalLatticeOpen (l := l) T b

/-- The actual S994FiniteInput, with finiteness supplied by S1008. -/
noncomputable def s1018FiniteInput
    (hopen : S1018OpennessInput (l := l) T) :
    S994FiniteInput (l := l) T where
  L := fun b => s994ActualLinearization (l := l) T b
  qPilot_pos := fun b => by
    have hp := s1007QPilotImage_measure_pos_of_open (l := l) T b (hopen b)
    dsimp only [s994H, s994QPilotImage, s994ActualLinearization,
      s1004H, s1004QPilotImage, s1004E] at hp ⊢
    exact hp
  hull_finite := fun b => by
    have hf := s1008Hull_measure_lt_top (l := l) T b
    dsimp only [s994H, s994Hull, s994ActualLinearization,
      s1004H, s1004Hull, s1004E] at hf ⊢
    exact hf

/-- Actual S994FiniteInput, with S1023 openness and S1008 hull finiteness. -/
noncomputable def s1018FiniteInput_actual : S994FiniteInput (l := l) T :=
  s1018FiniteInput (l := l) T
    (fun b => s923FractionalLatticeOpen_actual (l := l) T b)

/-- Reduced exact condition is now actual: no openness field remains. -/
def S1018FiniteInputReduced : Prop :=
  Nonempty (S994FiniteInput (l := l) T)

theorem s1018FiniteInput_nonempty_actual :
    Nonempty (S994FiniteInput (l := l) T) :=
  ⟨s1018FiniteInput_actual (l := l) T⟩

/-- The old explicit hull-finiteness field is no longer an independent exact
condition: it is discharged by S1008. -/
theorem s1018HullFiniteness_actual
    (b : Bad (nativePlaceSelection T)) :
    (s994H (l := l) T b (s994ActualLinearization (l := l) T b)).measure
      (s994Hull (l := l) T b (s994ActualLinearization (l := l) T b)) < ⊤ := by
  have hf := s1008Hull_measure_lt_top (l := l) T b
  dsimp only [s994H, s994Hull, s994ActualLinearization,
    s1004H, s1004Hull, s1004E] at hf ⊢
  exact hf

end LeanFormal.IUT.XiFPaper.S1018S995ReducedConditionsActual

end
