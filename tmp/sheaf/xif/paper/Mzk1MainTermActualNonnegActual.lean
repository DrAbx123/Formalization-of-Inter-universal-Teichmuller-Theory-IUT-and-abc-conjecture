/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P3DictDCurveDataSourceActual
import tmp.sheaf.xif.paper.Mzk1P3DictDLogDiscActual
import Mathlib.Tactic
/-! # #7 actual main-term nonnegativity from CurveData disc/cond -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1MainTermActualNonnegActual
open LeanFormal.IUT LeanFormal.IUT.XiFPaper.Mzk1P3DictDCurveDataSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogDiscActual
universe u
variable {l : PrimeGeFive} {ι : Type u}
theorem log_natCast_nonneg (n : Nat) : 0 ≤ Real.log (n : Real) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt h)
theorem mainTerm_nonneg_actual (M : CurveData ι) (E : ι) :
    0 ≤ (1 / 4 : Real) * (l.value : Real) *
      (Real.log (M.disc E : Real) + Real.log (M.cond E : Real)) := by
  have hl : 0 < (l.value : Real) := by exact_mod_cast l.prime.pos
  have hd : 0 ≤ Real.log (M.disc E : Real) := log_natCast_nonneg _
  have hf : 0 ≤ Real.log (M.cond E : Real) := log_natCast_nonneg _
  nlinarith
def rows : List String := ["log_natCast_nonneg", "mainTerm_nonneg_actual (disc/cond)"]
theorem rows_length : rows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1MainTermActualNonnegActual
end