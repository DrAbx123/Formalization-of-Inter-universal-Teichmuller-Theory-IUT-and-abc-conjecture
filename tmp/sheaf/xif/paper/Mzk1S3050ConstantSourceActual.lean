import tmp.sheaf.xif.paper.S3050StepVQExpansionActual
import Mathlib.Tactic

/-!
# Mzk1S3050ConstantSourceActual

Task-91: exact local conversion for the S3050 unit.

S3050Unit p jValue l = (localNormOrder p jValue)/(2*l) * log p.
Multiplying by 2*l gives the local signed q-log
  localSignedQLog = localNormOrder p jValue * log p
(= ord J * log p; with qOrder = -ord J this is -qOrder log p).

This is only the LOCAL conversion.  No theorem here identifies it with
S2921Q: S2921Q is the global line-bundle log of qPilotLineBundleExtended
(S2736QPilotLineBundleHweightvol:19-22; S2921HeightBridgeActual:28-31), while
S3050Unit is a one-factor local ord J expression.  The missing source object is
the local-to-global q-pilot line-bundle exponent/weight identity; see
coord/P3-EXACT-REDUCTION.md.

No sorry/axiom/True/PUnit/toy.  New file: report to Lead for extra-targets.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1S3050ConstantSourceActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S3050StepVQExpansionActual

/-- The local signed q-log attached to the same jValue: ord(J) * log p. -/
noncomputable def localSignedQLog {K : Type*} [Norm K]
    (p : Nat) (jValue : K) : Real :=
  localNormOrder p jValue * Real.log (p : Real)

/-- Exact local conversion: (2l) * S3050Unit = localSignedQLog. -/
theorem twoL_mul_S3050Unit_eq_localSignedQLog {K : Type*} [Norm K]
    (p : Nat) (jValue : K) (l : Nat) (hl : l ≠ 0) :
    (2 * (l : Real)) * S3050Unit p jValue l =
      localSignedQLog p jValue := by
  have hlR : (2 * (l : Real)) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (by norm_num) hl)
  unfold S3050Unit localSignedQLog
  push_cast
  field_simp [hlR]

/-- S3050Unit is the paper signed c_root log: localSignedQLog/(2l). -/
theorem S3050Unit_eq_localSignedQLog_div {K : Type*} [Norm K]
    (p : Nat) (jValue : K) (l : Nat) (hl : l ≠ 0) :
    S3050Unit p jValue l =
      localSignedQLog p jValue / (2 * (l : Real)) := by
  have hlR : (2 * (l : Real)) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (by norm_num) hl)
  unfold S3050Unit localSignedQLog
  push_cast
  field_simp [hlR]

/-- The global S2921Q side is NOT defined here; this records the exact missing
source target as a named proposition, not as a proved equality. -/
def S3050ToS2921GlobalSourceTarget (S2921Q : Real) (l : Nat)
    (localSum : Real) : Prop :=
  S2921Q = -((2 * (l : Real)) * localSum)

#check twoL_mul_S3050Unit_eq_localSignedQLog
#check S3050Unit_eq_localSignedQLog_div
#check S3050ToS2921GlobalSourceTarget

end LeanFormal.IUT.XiFPaper.Mzk1S3050ConstantSourceActual

end
