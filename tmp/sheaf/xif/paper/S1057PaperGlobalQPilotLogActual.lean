import tmp.sheaf.xif.paper.S1050PerBQPilotCoefficientAuditActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1057PaperGlobalQPilotLogActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S1050PerBQPilotCoefficientAuditActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Paper global qPilot log: the Bad-weighted sum of the paper finite per-b
s994VR, NOT the classical perBQPilotLog weighted sum. -/
noncomputable def paperGlobalQPilotLog (In : S994FiniteInput T) : Real :=
  weightedPaperV (l := l) T (s994VR (l := l) T In)

/-- Definitional weighted-sum formula. -/
theorem paperGlobalQPilotLog_eq_weighted (In : S994FiniteInput T) :
    paperGlobalQPilotLog (l := l) T In =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * s994VR (l := l) T In b :=
  rfl

/-- The paper object is exactly S1050's paper global qPilot. -/
theorem paperGlobalQPilotLog_eq_s1050 (In : S994FiniteInput T) :
    paperGlobalQPilotLog (l := l) T In =
      s1050PaperGlobalQPilotLog (l := l) T In :=
  rfl

/-- Classical global qPilot is a different object: its per-b input is
perBQPilotLog, not s994VR.  This is the exact object distinction. -/
theorem paperGlobalVsClassical :
    (∀ b : Bad (nativePlaceSelection T),
      perBQPilotLog (l := l) T b = s994VR (l := l) T In b) ->
      paperGlobalQPilotLog (l := l) T In = globalQPilotLog (l := l) T := by
  intro h
  unfold paperGlobalQPilotLog globalQPilotLog weightedPaperV
  apply Finset.sum_congr rfl
  intro b _
  rw [h b]

/-- Nonempty actual value with its defining equation. -/
theorem paperGlobalQPilotLog_nonempty (In : S994FiniteInput T) :
    Nonempty {x : Real // x = paperGlobalQPilotLog (l := l) T In} :=
  ⟨⟨paperGlobalQPilotLog (l := l) T In, rfl⟩⟩

/-- Well-defined: existence and uniqueness of the paper global qPilot scalar. -/
theorem paperGlobalQPilotLog_existsUnique (In : S994FiniteInput T) :
    ∃! x : Real, x = paperGlobalQPilotLog (l := l) T In :=
  ⟨paperGlobalQPilotLog (l := l) T In, rfl, fun y hy => hy⟩

/-- Exact object condition: paper global qPilot is the weighted s994VR sum. -/
def S1057PaperGlobalObjectCondition (In : S994FiniteInput T) : Prop :=
  paperGlobalQPilotLog (l := l) T In =
    weightedPaperV (l := l) T (s994VR (l := l) T In)

theorem S1057PaperGlobalObjectCondition_actual
    (In : S994FiniteInput T) :
    S1057PaperGlobalObjectCondition (l := l) T In :=
  rfl

/-- Exact identification with the classical object, recorded but not asserted
as an unconditional equality. -/
def S1057ClassicalPaperExact (In : S994FiniteInput T) : Prop :=
  paperGlobalQPilotLog (l := l) T In = globalQPilotLog (l := l) T

end LeanFormal.IUT.XiFPaper.S1057PaperGlobalQPilotLogActual

end
