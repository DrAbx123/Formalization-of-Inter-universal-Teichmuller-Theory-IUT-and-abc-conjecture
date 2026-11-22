import tmp.sheaf.n8.closure.PaperP6Final

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperP6Target2

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PK : Type := LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry.PaperKf S

/-- Candidate paper-level P6 target. -/
def PaperP6Target : Prop :=
  ∃ qLog thetaLog : ℝ,
    qLog = Real.log ‖(LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry.qUnit S : PK S)‖ ∧
    thetaLog = LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry.thetaLogVolume S ∧
    qLog ≤ thetaLog ∧
    (thetaLog : WithTop ℝ) < ⊤

theorem paperP6Target_actual : PaperP6Target S :=
  ⟨Real.log ‖(LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry.qUnit S : PK S)‖,
    LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry.thetaLogVolume S,
    rfl, rfl,
    LeanFormal.IUT.N8Closure.PaperP6ComparisonActual.paper_log_norm_le_thetaLogVolume S,
    LeanFormal.IUT.N8Closure.PaperP6Final.thetaLogVolume_lt_top S⟩

end LeanFormal.IUT.N8Closure.PaperP6Target2

end
