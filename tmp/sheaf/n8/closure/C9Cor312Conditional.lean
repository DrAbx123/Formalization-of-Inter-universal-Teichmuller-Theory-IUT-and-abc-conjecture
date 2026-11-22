import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.N8Closure.C9Cor312Conditional

structure Theorem311Full where
  Output : Type
  possibleOutputs : Set Output
  logVol : Output → ℝ
  qPilotOutput : Output
  qPilotOutput_mem : qPilotOutput ∈ possibleOutputs

structure Prop39 (T : Theorem311Full) where
  qLog : ℝ
  qLog_eq : qLog = T.logVol T.qPilotOutput

structure Remark395 (T : Theorem311Full) where
  R : Set ℝ
  R_eq : R = T.logVol '' T.possibleOutputs
  h : ℝ
  hull_upper : ∀ x, x ∈ R → x ≤ h

structure ThreeAssumptions where
  T311 : Theorem311Full
  P39 : Prop39 T311
  R395 : Remark395 T311

/-- Conditional C1: from the three source assumptions, Q <= h. -/
theorem cor312 (A : ThreeAssumptions) : A.P39.qLog ≤ A.R395.h := by
  have hq : A.P39.qLog ∈ A.R395.R := by
    rw [A.R395.R_eq, A.P39.qLog_eq]
    exact ⟨A.T311.qPilotOutput, A.T311.qPilotOutput_mem, rfl⟩
  exact A.R395.hull_upper A.P39.qLog hq

#print axioms cor312

end LeanFormal.IUT.N8Closure.C9Cor312Conditional

end