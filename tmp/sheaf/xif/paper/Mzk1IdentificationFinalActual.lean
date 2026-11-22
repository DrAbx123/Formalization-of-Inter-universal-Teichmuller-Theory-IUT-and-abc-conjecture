/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A837 hull: normalization ruling and identification status

Green definition: `localDifferentPaperOrder = localDifferentOrder / e`
(`IntegralTraceDualTensorInclusion.lean:701-703`, `e = logShellRamificationExponent`).
So the paper `d` is `v/e` (NOT `v/(e f)`); the integer different lower
`v >= e-1` would give `d >= (e-1)/e = 1 - 1/e` exactly, with no factor `f`.

However the integer lower `v >= e-1` itself is not in the repo
(`Ideal.different` construction absent), so it remains an explicit input.

Pointwise radius: green `unitLogLattice_subset_logShellPaperBetaElement_smul_integers`
gives `||x|| <= ||beta|| = p^(paperB)` for log-units `x`; scaling by `(2p)^-1`
adds the normalization `1 + [p=2]`.  Formalizing `-ordp y <= paperB + corr`
requires the exact sign convention of `logShellRadius` (integer `ordp` vs
normalized `ordp/e`) and is NOT done here; the sSup step is already proved
in `Mzk1IdentificationCompletedActual`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1IdentificationFinalActual

/-- Paper different order is `v/e` (green definition). -/
def paperDifferentOrder (v e : ℝ) : ℝ := v / e

theorem paperDifferentOrder_eq (v e : ℝ) : paperDifferentOrder v e = v / e := rfl

/-- Integer different lower `v >= e-1` gives the paper lower `1 - 1/e` under
the green normalization `d = v/e`. -/
theorem paperDifferentOrder_ge_one_sub_inv (v e : ℝ) (he : 0 < e) (h : e - 1 ≤ v) :
    paperDifferentOrder v e ≥ 1 - 1 / e := by
  unfold paperDifferentOrder
  have heq : 1 - 1 / e = (e - 1) / e := by field_simp [ne_of_gt he]
  rw [heq]
  exact div_le_div_of_nonneg_right h (le_of_lt he)

/-- Integer different lower predicate (the missing `Ideal.different` step). -/
def DifferentIntegerLower (v e : ℝ) : Prop := e - 1 ≤ v

/-- Fact 2 from the integer lower + `a >= 1/e`. -/
theorem different_add_a_ge_one (v e a : ℝ) (he : 0 < e) (h : e - 1 ≤ v)
    (ha : 1 / e ≤ a) :
    paperDifferentOrder v e + a ≥ 1 := by
  have hd : paperDifferentOrder v e ≥ 1 - 1 / e := paperDifferentOrder_ge_one_sub_inv v e he h
  linarith

/-- Pointwise radius interface (green containment gives `||x|| <= p^paperB`;
the `(2p)^-1` scaling correction is `1+[p=2]`). -/
def RadiusPointwiseBound (ordp : ℝ) (paperB : ℝ) (pIsTwo : Bool) : Prop :=
  -ordp ≤ paperB + 1 + (if pIsTwo then 1 else 0 : ℝ)

theorem radius_bound_of_pointwise (ordp paperB : ℝ) (pIsTwo : Bool)
    (h : RadiusPointwiseBound ordp paperB pIsTwo) :
    -ordp ≤ paperB + 1 + (if pIsTwo then 1 else 0 : ℝ) := h

def finalRows : List (String × String × String) :=
  [ ("paper d normalization", "localDifferentPaperOrder = localDifferentOrder / e (green def)", "CONFIRMED: d = v/e, not v/(ef)"),
    ("different lower input", "v >= e-1 (different contains pi^(e-1))", "INPUT (not in repo)"),
    ("d >= 1-1/e", "v/e >= (e-1)/e = 1-1/e", "PROVED (paperDifferentOrder_ge_one_sub_inv)"),
    ("fact2", "d + a >= 1 when v>=e-1 and a>=1/e", "PROVED (different_add_a_ge_one)"),
    ("radius pointwise", "-ordp y <= paperB + 1+[p=2]", "INTERFACE (RadiusPointwiseBound); green gives ||x||<=p^paperB, sign/ordp convention missing"),
    ("sSup step", "pointwise => sSup <= bound", "PROVED elsewhere (Mzk1IdentificationCompletedActual.sSup_image_le_of_pointwise)"),
    ("normalization correction", "(2p)^-1 gives 1+[p=2]", "DEF (normalizationCorrection, earlier)") ]

theorem finalRows_length : finalRows.length = 7 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1IdentificationFinalActual.paperDifferentOrder_ge_one_sub_inv
#print axioms LeanFormal.IUT.XiFPaper.Mzk1IdentificationFinalActual.different_add_a_ge_one

end LeanFormal.IUT.XiFPaper.Mzk1IdentificationFinalActual

end