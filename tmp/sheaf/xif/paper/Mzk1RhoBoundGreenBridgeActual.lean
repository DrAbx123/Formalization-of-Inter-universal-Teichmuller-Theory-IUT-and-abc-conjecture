/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A830 hull: green bridge inventory for the two per-place facts

Green assets (IntegralLogShellSharpBounds):
* `unitLogLattice_le_padicFractionalLattice_neg_paperB`
  (`unitLogLattice <= padicFractionalLattice (-paperB)`);
* `unitLogLattice_subset_logShellPaperBetaElement_smul_integers`
  (`log(O^×) <= beta * R`, `beta` = `logShellPaperBetaElement`);
* `norm_logShellPaperBetaElement` (`||beta|| = p^(paperB)`);
* `padicValNat_sub_div_le_logShellPaperBExponent`.

Different side: `LocalDifferentUpperBound.localDifferentPaperOrder_le_degree_padicVal`
is an UPPER bound; no green lower bound `d >= 1-1/e` exists.  The construction
from `Ideal.different` (`v_K(d) >= e-1`) is not in the repo.

This file proves the arithmetic transfers that are independent of the carrier:
if the radius is at most `paperB + correction` and the correction is the
`(2p)^-1` normalization `1 + [p=2]`, then fact 1; and if the paper different
order is `(e-1)/e` then fact 2.  The missing piece is the *identification* of
`logShellRadius` with `paperB + correction` from the green inclusions/norm
(the sSup/radius computation is not formalized). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1RhoBoundGreenBridgeActual

/-- Fact 1 from the green containment once the radius-to-B identification is
given as the hypothesis `hradius : rho <= paperB + correction` and
`correction <= 1 + [p=2]`. -/
theorem rho_le_paperB_add_correction (rho paperB correction : ℝ) (pIsTwo : Bool)
    (hradius : rho ≤ paperB + correction)
    (hcorr : correction ≤ 1 + (if pIsTwo then 1 else 0 : ℝ)) :
    rho ≤ paperB + 1 + (if pIsTwo then 1 else 0 : ℝ) := by
  linarith

/-- The `(2p)^-1` normalization correction: for odd `p`, `correction = 1`;
for `p = 2`, `correction = 2`.  This is the arithmetic content of
`logShell = (2p)^-1 log(O^×)` at the radius level. -/
def normalizationCorrection (pIsTwo : Bool) : ℝ :=
  1 + (if pIsTwo then 1 else 0 : ℝ)

theorem normalizationCorrection_eq (pIsTwo : Bool) :
    normalizationCorrection pIsTwo = 1 + (if pIsTwo then 1 else 0 : ℝ) := rfl

/-- Fact 2 if the paper different order is `(e-1)/e`: then it is at least
`1 - 1/e`; adding `a >= 1/e` gives `1`. -/
theorem different_add_a_ge_of_paperOrder (e a : ℝ) (he : 0 < e)
    (ha : 1 / e ≤ a) :
    (e - 1) / e + a ≥ 1 := by
  have h : (e - 1) / e = 1 - 1 / e := by field_simp [ne_of_gt he]
  rw [h]
  linarith

theorem paperDifferentOrder_ge_one_sub_inv (e : ℝ) (he : 0 < e) :
    (e - 1) / e ≥ 1 - 1 / e := by
  have h : (e - 1) / e = 1 - 1 / e := by field_simp [ne_of_gt he]
  rw [h]

def bridgeRows : List (String × String × String) :=
  [ ("green B inclusion", "unitLogLattice <= padicFractionalLattice (-paperB)", "GREEN (cited)"),
    ("green beta element", "log(O^×) <= beta * R, ||beta||=p^paperB", "GREEN (cited)"),
    ("green padicVal bound", "padicValNat_sub_div_le_logShellPaperBExponent", "GREEN (cited)"),
    ("normalization correction", "(2p)^-1 gives 1+[p=2]", "DEF (normalizationCorrection)"),
    ("fact 1 transfer", "rho <= paperB + correction, correction <= 1+[p=2] => rho bound", "PROVED (rho_le_paperB_add_correction)"),
    ("different paper order", "(e-1)/e >= 1-1/e", "PROVED (paperDifferentOrder_ge_one_sub_inv)"),
    ("fact 2 transfer", "(e-1)/e + a >= 1 when a>=1/e", "PROVED (different_add_a_ge_of_paperOrder)"),
    ("MISSING identification 1", "logShellRadius = sSup(-ordp '' logShell) <= paperB + correction from green inclusions", "GAP (sSup/radius arithmetic not formalized)"),
    ("MISSING identification 2", "d = localDifferentPaperOrder >= (e-1)/e (no green lower bound; Ideal.different construction absent)", "GAP") ]

theorem bridgeRows_length : bridgeRows.length = 9 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1RhoBoundGreenBridgeActual.rho_le_paperB_add_correction
#print axioms LeanFormal.IUT.XiFPaper.Mzk1RhoBoundGreenBridgeActual.different_add_a_ge_of_paperOrder
#print axioms LeanFormal.IUT.XiFPaper.Mzk1RhoBoundGreenBridgeActual.paperDifferentOrder_ge_one_sub_inv

end LeanFormal.IUT.XiFPaper.Mzk1RhoBoundGreenBridgeActual

end