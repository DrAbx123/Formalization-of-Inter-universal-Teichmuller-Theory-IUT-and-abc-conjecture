import tmp.sheaf.xif.paper.Mzk1P3DictionaryActual
import Mathlib.Tactic

/-! # CONDITIONAL: L6 implies paper box (DICT-C one direction) -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictCBoxFromL6Actual

open LeanFormal.IUT.XiFPaper.Mzk1P3DictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperStepVBoxActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual

/-- L6 + S,T>=0 + l>=5 implies the paper box. -/
theorem boxSlack_nonneg_of_L6
    (C : PrimeConductorCurve) (l D Q S Tstar : Real)
    (hl : 5 <= l) (hS : 0 <= S) (hT : 0 <= Tstar)
    (hL6 : L6ReducedInequality C l D) :
    0 <= boxSlack l D Q S Tstar := by
  have hlpos : 0 < l := by linarith
  have hTpos : 0 < T l := T_pos_of_five_le hl
  have hlogp : 0 <= Real.log (C.p : Real) := by
    have hp1 : (1 : Real) <= (C.p : Real) := by exact_mod_cast C.hp.one_lt.le
    exact Real.log_nonneg hp1
  have he : 0 <= (C.e : Real) * Real.log (C.p : Real) :=
    mul_nonneg (by positivity) hlogp
  have hTD : 0 <= T l * D := le_trans he hL6
  have hD : 0 <= D := (mul_nonneg_iff_of_pos_left hTpos).mp hTD
  rw [boxSlack_eq l D Q S Tstar (ne_of_gt hlpos)]
  have h1 : 0 <= (1 / l) * D := mul_nonneg (one_div_nonneg.mpr hlpos.le) hD
  have h2 : 0 <= (1 / l) * S := mul_nonneg (one_div_nonneg.mpr hlpos.le) hS
  have hcoef : 0 <= (2 * l - 10) / 3 := by nlinarith
  have h3 : 0 <= ((2 * l - 10) / 3) * Tstar := mul_nonneg hcoef hT
  linarith

#check boxSlack_nonneg_of_L6
end LeanFormal.IUT.XiFPaper.Mzk1P3DictCBoxFromL6Actual
end
