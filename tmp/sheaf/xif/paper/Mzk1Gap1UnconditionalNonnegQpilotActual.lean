/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1CorrectedGap1UnconditionalQpilotActual
import Mathlib.Tactic

/-! # Mzk1Gap1UnconditionalNonnegQpilotActual — Gap1 unconditional for 0 <= eps (A669)

Paper-parameter form of the corrected Gap-1 equivalence: for `0 <= epsilon`
(hence `0 < 1+epsilon`), the multiplicative comparison and the log inequality are
equivalent unconditionally (positive `h`, `base`, `f`). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap1UnconditionalNonnegQpilotActual

universe u

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalQpilotActual
open scoped BigOperators

theorem gap1_unconditional_nonneg {ι : Type u} [Fintype ι] {h epsilon : Real}
    (f : ι → Real) (e : ι → Nat) (base : Real) (hf : ∀ i, 0 < f i)
    (hb : 0 < base) (hh : 0 < h) (hε : 0 ≤ epsilon) :
    (h ≤ (1 + epsilon) * correctedVol f e base) ↔
      (Real.log h ≤ Real.log (1 + epsilon) +
        (Real.log base - ∑ i, (e i : Real) * Real.log (f i))) :=
  corrected_gap1_unconditional f e base hf hb hh (by linarith)

theorem gap1_unconditional_nonneg_from_log {ι : Type u} [Fintype ι] {h epsilon : Real}
    (f : ι → Real) (e : ι → Nat) (base : Real) (hf : ∀ i, 0 < f i)
    (hb : 0 < base) (hh : 0 < h) (hε : 0 ≤ epsilon)
    (hlog : Real.log h ≤ Real.log (1 + epsilon) +
        (Real.log base - ∑ i, (e i : Real) * Real.log (f i))) :
    h ≤ (1 + epsilon) * correctedVol f e base :=
  (gap1_unconditional_nonneg f e base hf hb hh hε).mpr hlog

theorem gap1_unconditional_nonneg_log {ι : Type u} [Fintype ι] {h epsilon : Real}
    (f : ι → Real) (e : ι → Nat) (base : Real) (hf : ∀ i, 0 < f i)
    (hb : 0 < base) (hh : 0 < h) (hε : 0 ≤ epsilon)
    (h1 : h ≤ (1 + epsilon) * correctedVol f e base) :
    Real.log h ≤ Real.log (1 + epsilon) +
      (Real.log base - ∑ i, (e i : Real) * Real.log (f i)) :=
  (gap1_unconditional_nonneg f e base hf hb hh hε).mp h1

def gap1UnconditionalRows : List (String × String) :=
  [ ("Gap1 equivalence for 0 <= eps", "PROVED"),
    ("log-input direction", "PROVED"),
    ("multiplicative-input log form", "PROVED") ]

theorem gap1UnconditionalRows_length : gap1UnconditionalRows.length = 3 := rfl

#check gap1_unconditional_nonneg
#check gap1UnconditionalRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Gap1UnconditionalNonnegQpilotActual
end
