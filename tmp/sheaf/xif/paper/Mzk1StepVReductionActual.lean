import tmp.sheaf.xif.paper.S3050StepVQExpansionActual
import Mathlib.Tactic

/-!
# Mzk1StepVReductionActual

P3 exact-reduction source-level interface (task-89).

This file only records two things that are genuinely encoded by the existing
interfaces:

* the signed target is equivalent to M >= 0 by pure real algebra;
* S3050Unit is the paper c_root unit: (ord J)/(2l) * log p, not c_norm.

It does NOT assert S3050QUnitIdentification as a paper identification: for a
nonzero Q that proposition is trivially true with c = unit/Q, so it carries no
paper constant.  The meaningful paper statement remains S3079PaperConstantTarget
or a source identity between StepV and S2921Q; both are open here.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1StepVReductionActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S3050StepVQExpansionActual

/-- The target M = V + gap - (sF - 1) A. -/
def TargetM (V gap sF A : Real) : Real :=
  V + gap - (sF - 1) * A

/-- The signed target -A <= -R. -/
def TargetSigned (A R : Real) : Prop :=
  -A <= -R

/-- Signed target is exactly M >= 0 for M = A - R. -/
theorem signed_ineq_iff_M_nonneg {A R : Real} :
    TargetSigned A R <-> 0 <= A - R := by
  unfold TargetSigned
  constructor <;> intro h <;> linarith

/-- If R is the signed Theta volume, M = A - R. -/
theorem targetM_eq_A_sub_R {V gap sF A R : Real}
    (hR : R = -(V + gap - sF * A)) :
    TargetM V gap sF A = A - R := by
  unfold TargetM
  linarith

/-- S3050Unit is the paper c_root unit: (ord J)/(2l) log p = -c_root(q) log p. -/
theorem stepVUnit_eq_rootCoefficient {K : Type*} [Norm K]
    (p : Nat) (jValue : K) (l : Nat) :
    S3050Unit p jValue l =
      (localNormOrder p jValue / (2 * (l : Real))) * Real.log (p : Real) := by
  unfold S3050Unit
  push_cast
  ring

end LeanFormal.IUT.XiFPaper.Mzk1StepVReductionActual

end
