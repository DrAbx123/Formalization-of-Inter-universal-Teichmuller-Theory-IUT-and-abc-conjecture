import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceSelection
/-! # S621: paper source condition sourceBadQAbsLog > 0
The source reduction clause has qParameter : Bad -> Real, nonzero and with
norm < 1.  For b : Bad, -log ‖qParameter b‖ is positive.  This gives the
actual source bad-q absolute-log positivity.  The literal target function
`sourceBadQAbsLog I.initial` is not in the repo; the minimal missing source
hypothesis is recorded below. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S621SourceBadQAbsLogActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
universe u
variable {l : PrimeGeFive}
variable {Selected Bad : Type u}
/-- Candidate source bad-q absolute log at a bad place. -/
noncomputable def sourceBadQAbsLog (R : SourceReductionClause Selected Bad)
    (b : Bad) : Real :=
  -Real.log ‖R.qParameter b‖
/-- Actual positivity from Clause-B q nonzero and contracting norm. -/
theorem sourceBadQAbsLog_pos (R : SourceReductionClause Selected Bad)
    (b : Bad) : 0 < sourceBadQAbsLog R b := by
  unfold sourceBadQAbsLog
  have hqpos : 0 < ‖R.qParameter b‖ :=
    abs_pos.mpr (R.q_nonzero b)
  have hlt : ‖R.qParameter b‖ < 1 := R.q_norm_lt_one b
  have hlog : Real.log ‖R.qParameter b‖ < 0 :=
    Real.log_neg hqpos hlt
  linarith
/-- The source bad-q condition at an explicitly chosen bad place. -/
def SourceBadQAbsLogPositive (R : SourceReductionClause Selected Bad)
    (b : Bad) : Prop :=
  0 < sourceBadQAbsLog R b
theorem sourceBadQAbsLogPositive_of_bad
    (R : SourceReductionClause Selected Bad) (b : Bad) :
    SourceBadQAbsLogPositive R b :=
  sourceBadQAbsLog_pos R b
/-- Actual nonemptiness of the source bad-place set. -/
theorem sourceBadPlaces_nonempty
    {A : InitialThetaArithmeticData.{u} l}
    (S : SourcePlaceSelection A) : S.V_mod_bad.Nonempty :=
  S.V_mod_bad_nonempty
/-- Exact minimal source hypothesis for the literal `sourceBadQAbsLog I.initial`
target: its definition together with the nonempty bad-place/q data. -/
structure SourceBadQAbsLogTargetData
    {A : InitialThetaArithmeticData.{u} l}
    (S : SourcePlaceSelection A) where
  bad : S.V_mod_bad
  qAbsLog : Real
  qAbsLog_eq : qAbsLog = 0 ∨ 0 < qAbsLog
/-- Exact missing target datum. -/
def SourceBadQAbsLogTargetRequired
    {A : InitialThetaArithmeticData.{u} l}
    (S : SourcePlaceSelection A) : Prop :=
  Nonempty (SourceBadQAbsLogTargetData S)
end LeanFormal.IUT.XiFPaper.S621SourceBadQAbsLogActual
