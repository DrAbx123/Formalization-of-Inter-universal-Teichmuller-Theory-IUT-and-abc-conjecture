import tmp.sheaf.xif.paper.S1037GlobalQPilotAuditActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1047GlobalQPilotLogActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual
open LeanFormal.IUT.XiFPaper.S1037GlobalQPilotAuditActual
open LeanFormal.IUT.XiFPaper.S919GlobalWeightedInequalityActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Paper global qPilot log: the actual Bad-place weighted sum. -/
noncomputable def GlobalQPilotLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * perBQPilotLog (l := l) T b

/-- The definition is exactly the S706/PaperLevelXiFTargetProof global qPilot
log. -/
theorem GlobalQPilotLog_eq_globalQPilotLog :
    GlobalQPilotLog (l := l) T = globalQPilotLog (l := l) T :=
  rfl

/-- Well-defined weighted sum formula. -/
theorem GlobalQPilotLog_eq_weighted :
    GlobalQPilotLog (l := l) T =
      weightedPaperV (l := l) T (perBQPilotLog (l := l) T) := by
  unfold GlobalQPilotLog weightedPaperV
  rfl

/-- The global qPilot log is an actual real value (nonempty). -/
theorem GlobalQPilotLog_nonempty : Nonempty {x : Real // x = GlobalQPilotLog (l := l) T} :=
  ⟨⟨GlobalQPilotLog (l := l) T, rfl⟩⟩

/-- Existence and uniqueness of the global qPilot scalar. -/
theorem GlobalQPilotLog_existsUnique :
    ∃! x : Real, x = GlobalQPilotLog (l := l) T :=
  ⟨GlobalQPilotLog (l := l) T, rfl, fun y hy => hy⟩

/-- Exact object condition: the global qPilot is the Bad-weighted sum, not the
single local C3.q. -/
def S1047ExactObjectCondition : Prop :=
  GlobalQPilotLog (l := l) T =
    weightedPaperV (l := l) T (perBQPilotLog (l := l) T)

theorem S1047ExactObjectCondition_actual :
    S1047ExactObjectCondition (l := l) T :=
  GlobalQPilotLog_eq_weighted (l := l) T

end LeanFormal.IUT.XiFPaper.S1047GlobalQPilotLogActual

end
