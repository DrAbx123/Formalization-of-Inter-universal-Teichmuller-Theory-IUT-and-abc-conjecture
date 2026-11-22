import tmp.sheaf.xif.paper.S1041GlobalizedAssemblyActual
import tmp.sheaf.xif.PaperQPilotObject
/-! # S1042: actual S1041GlobalQParameterCard
qParameter := exp(O.qPilotLogVolume).  Positivity and log-nonvanishing are
automatic; the absolute-value identity uses negativity of the source qPilot
sign, which follows from nonempty bad places. -/
noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S1042GlobalQParameterCardActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S1041GlobalizedAssemblyActual
open MeasureTheory
universe ua uv upi umon ui uL uC uG uX uLabel u uC3 uD3 uM uP
variable {l : PrimeGeFive}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G' : Type uG} [Group G'] [TopologicalSpace G']
variable {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]
variable (P : PaperSignedHull X label)
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable (O : PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
  (Label := Label) (Choice := Choice) (I := I) G' envStrip)
/-- Exact minimal sign input: nonempty source bad places. -/
def S1042ExactInput : Prop := Nonempty I.initial.badPlaces
theorem qPilotLogVolume_neg (hbad : Nonempty I.initial.badPlaces) :
    O.qPilotLogVolume < 0 := by
  rw [O.qPilotLogVolume_eq]
  exact sourceQPilotSignedLog_neg_of_nonempty I.initial hbad
theorem qPilotLogVolume_ne_zero (hbad : Nonempty I.initial.badPlaces) :
    O.qPilotLogVolume ≠ 0 :=
  ne_of_lt (qPilotLogVolume_neg O hbad)
/-- Actual global qParameter card. -/
noncomputable def s1042GlobalQParameterCard
    (hbad : Nonempty I.initial.badPlaces) :
    S1041GlobalQParameterCard (l := l) O where
  qParameter := Real.exp O.qPilotLogVolume
  qParameter_pos := Real.exp_pos _
  qParameter_log_ne_zero := by
    rw [Real.log_exp]
    exact qPilotLogVolume_ne_zero O hbad
  qPilotLogVolume_eq := by
    rw [Real.log_exp]
    have hneg := qPilotLogVolume_neg O hbad
    rw [abs_of_neg hneg]
    ring
theorem s1042GlobalQParameterCard_actual
    (hbad : Nonempty I.initial.badPlaces) :
    Nonempty (S1041GlobalQParameterCard (l := l) O) :=
  ⟨s1042GlobalQParameterCard O hbad⟩
end LeanFormal.IUT.XiFPaper.S1042GlobalQParameterCardActual