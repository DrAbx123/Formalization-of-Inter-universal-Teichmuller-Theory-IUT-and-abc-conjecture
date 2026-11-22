/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3050StepVQExpansionActual
import Mathlib.Tactic

/-! # A1065/A1070: S3050Unit scalar identity (separate file to avoid import conflict) -/

/-
| field | value |
|---|---|
| Status | PARTIAL (pure scalar algebra, no other imports) |
| 真证 | `S3050Unit_eq_log_norm_div` |
| 说明 | S3050Unit = -log||x||/(2l) (sign fixed in A1070) |
-/

noncomputable section
open LeanFormal.IUT.XiFPaper.S3050StepVQExpansionActual

namespace LeanFormal.IUT.XiFPaper.Mzk1S3050UnitScalarActual

/-- The StepV unit equals `-log ‖x‖/(2l)`. -/
theorem S3050Unit_eq_log_norm_div {K : Type*} [Norm K]
    (p : Nat) [Fact p.Prime] (l : Nat) (hl : l ≠ 0) (x : K) :
    S3050Unit p x l = - (Real.log ‖x‖) / (2 * (l : Real)) := by
  unfold S3050Unit localNormOrder
  have hp1 : (1 : Real) < (p : Real) := by
    exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hlogp : Real.log (p : Real) != 0 := (Real.log_pos hp1).ne'
  have hl' : (l : Real) != 0 := by exact_mod_cast hl
  have hl2 : (2 * (l : Real)) != 0 := by positivity
  field_simp [hlogp, hl2]
  ring

def s3050UnitRows : List (String × String) :=
  [ ("S3050Unit_eq_log_norm_div", "S3050Unit = -log||x||/(2l) (PROVED)") ]

theorem s3050UnitRows_length : s3050UnitRows.length = 1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1S3050UnitScalarActual