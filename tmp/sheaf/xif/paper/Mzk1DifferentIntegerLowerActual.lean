/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A842 hull: `v_K(different) >= e-1` — API inventory and gap

Repo API found (read-only search):
* Mathlib `differentIdeal R B` used by `ABCBridge/Arithmetic/RationalDifferent.lean`
  (`absNorm_differentIdeal`, `differentIdeal_eq_top_of_finrank_one`);
* `IntegralTraceDualLattice.coeSubmodule_differentIdeal_eq_inv_traceDual`
  (`differentIdeal = inverse codifferent` as submodules);
* `IntegralTraceDualLattice.differentIdeal_le_iff_traceForm_le_one`
  (ordering by trace-form bound);
* `DifferentTraceProduct.traceMultiplierIdeal_eq_differentIdeal`;
* `IntegralTraceDualTensorInclusion.localDifferentPaperOrder = localDifferentOrder / e`.

NO theorem `differentIdeal ⊇ (p^{e-1})` / `v_K(different) >= e-1` exists in the
repo.  The standard proof (trace of `π^{-(e-1)}`-dual lattice, or the
codifferent `⊆ π^{-(e-1)} O`) is not formalized.  This file records the
precise API and leaves the integer lower bound as an explicit input. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1DifferentIntegerLowerActual

/-- The desired integer lower bound, as an explicit input. -/
def DifferentIntegerLower (v e : ℤ) : Prop := e - 1 ≤ v

/-- Normalization statement (green definition): paper `d = v/e`; if `v >= e-1`
then `d >= 1 - 1/e`.  This part is proved in
`Mzk1IdentificationFinalActual.paperDifferentOrder_ge_one_sub_inv`. -/
def PaperNormalization (v e : ℝ) : ℝ := v / e

theorem paperNormalization_of_integer_lower (v e : ℝ) (he : 0 < e) (h : e - 1 ≤ v) :
    PaperNormalization v e ≥ 1 - 1 / e := by
  unfold PaperNormalization
  have heq : 1 - 1 / e = (e - 1) / e := by field_simp [ne_of_gt he]
  rw [heq]
  exact div_le_div_of_nonneg_right h he.le

/-- If the codifferent is contained in `π^{-(e-1)} O` (trace-dual bound),
then the different contains `π^{e-1} O`, i.e. `v >= e-1`; recorded as the
abstract implication to be instantiated from the API. -/
theorem different_integer_lower_of_codifferent (v e : ℤ)
    (h : DifferentIntegerLower v e) : DifferentIntegerLower v e := h

def lowerRows : List (String × String × String) :=
  [ ("Mathlib differentIdeal", "differentIdeal R B (RationalDifferent.lean)", "AVAILABLE (Mathlib)"),
    ("inverse codifferent", "coeSubmodule_differentIdeal_eq_inv_traceDual", "AVAILABLE (IntegralTraceDualLattice)"),
    ("trace-form order", "differentIdeal_le_iff_traceForm_le_one", "AVAILABLE (IntegralTraceDualLattice)"),
    ("tensor trace multiplier", "traceMultiplierIdeal_eq_differentIdeal", "AVAILABLE (DifferentTraceProduct)"),
    ("paper normalization", "localDifferentPaperOrder = localDifferentOrder / e", "AVAILABLE (IntegralTraceDualTensorInclusion)"),
    ("normalization consequence", "v >= e-1 => d = v/e >= 1-1/e", "PROVED (paperNormalization_of_integer_lower)"),
    ("MISSING", "differentIdeal >= span{pi^(e-1)} / v_K(different) >= e-1", "GAP (no repo theorem; trace-dual/codifferent inclusion not formalized)") ]

theorem lowerRows_length : lowerRows.length = 7 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1DifferentIntegerLowerActual.paperNormalization_of_integer_lower
#print axioms LeanFormal.IUT.XiFPaper.Mzk1DifferentIntegerLowerActual.different_integer_lower_of_codifferent

end LeanFormal.IUT.XiFPaper.Mzk1DifferentIntegerLowerActual

end