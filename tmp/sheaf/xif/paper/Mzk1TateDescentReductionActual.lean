/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import TateCurvesTheta.Converse.WeierstrassIso
import Mathlib.Tactic

/-! # Mzk1TateDescentReductionActual — (ii) reduced to a square-class condition (A814, qpilot)

The base-level realization gap (ii) of A801 is reduced to an explicit arithmetic square
condition using the vendor isomorphism criterion for curves with equal `j ≠ 0, 1728`
(`TateCurvesTheta.exists_variableChange_iff_isSquare`).

For elliptic curves `W W'` over a field with `2, 3 ≠ 0`, equal `j ≠ 0, 1728`:
  `(∃ C, C • W = W') ↔ IsSquare (γ(W') / γ(W))`,
where `γ(W) = -c₄(W)/c₆(W)` is the twist invariant.

Instantiated at `W = E_q` (the canonical Tate curve at the q-candidate) and `W' = X.curve`
(the input curve), the base-level realization of `TateComparisonData` is therefore
equivalent to `IsSquare (γ(X.curve) / γ(E_q))`.  The green source alignment supplies the
base `j`-equality and the Δ/c₄/c₆ normalization; what remains for (ii) is precisely the
square-class computation of `γ(X)/γ(E_q)`.

No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1TateDescentReductionActual

/-! ### 1. The square-class criterion -/

/-- **Descent square criterion** (vendor re-export): for elliptic curves with equal
`j ≠ 0, 1728` over a field with `2, 3 ≠ 0`, the existence of a base variable change
`C • W = W'` is equivalent to `γ(W')/γ(W)` being a square. -/
theorem tateDescent_iff_square {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic]
    (hj0 : W.j ≠ 0) (hj1728 : W.j ≠ 1728) (hj : W.j = W'.j) :
    (∃ C : WeierstrassCurve.VariableChange F, C • W = W') ↔
      IsSquare (TateCurvesTheta.gammaInvariant W' / TateCurvesTheta.gammaInvariant W) :=
  TateCurvesTheta.exists_variableChange_iff_isSquare h2 h3 W W' hj0 hj1728 hj

/-- The arithmetic descent condition for (ii): the twist invariants of the input curve and
the canonical Tate curve differ by a square. -/
def TateDescentCriterion {F : Type*} [Field F]
    (Ecanon Xcurve : WeierstrassCurve F) : Prop :=
  IsSquare (TateCurvesTheta.gammaInvariant Xcurve / TateCurvesTheta.gammaInvariant Ecanon)

/-- **Reduction of (ii)**: base-level realization `C • E_q = X.curve` is equivalent to the
square-class criterion `TateDescentCriterion E_q X.curve`. -/
theorem realization_iff_descentCriterion {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (Ecanon Xcurve : WeierstrassCurve F) [Ecanon.IsElliptic] [Xcurve.IsElliptic]
    (hj0 : Ecanon.j ≠ 0) (hj1728 : Ecanon.j ≠ 1728) (hj : Ecanon.j = Xcurve.j) :
    (∃ C : WeierstrassCurve.VariableChange F, C • Ecanon = Xcurve) ↔
      TateDescentCriterion Ecanon Xcurve :=
  tateDescent_iff_square h2 h3 Ecanon Xcurve hj0 hj1728 hj

/-- The J-invariant conditions in the form needed at the Tate curve: the canonical Tate
curve has `j ≠ 0, 1728` as explicit inputs of the criterion (kept as hypotheses, since the
canonical curve's j is not evaluated here). -/
theorem realization_iff_descentCriterion' {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (Ecanon Xcurve : WeierstrassCurve F) [Ecanon.IsElliptic] [Xcurve.IsElliptic]
    (hj0 : Ecanon.j ≠ 0) (hj1728 : Ecanon.j ≠ 1728) (hj : Xcurve.j = Ecanon.j) :
    (∃ C : WeierstrassCurve.VariableChange F, C • Ecanon = Xcurve) ↔
      TateDescentCriterion Ecanon Xcurve :=
  realization_iff_descentCriterion h2 h3 Ecanon Xcurve hj0 hj1728 hj.symm

/-! ### 2. Rows -/

def descentRows : List (String × String) :=
  [ ("vendor criterion: C • W = W' ↔ IsSquare (γ W' / γ W)", "PROVED (re-export)"),
    ("TateDescentCriterion definition (square-class of γ ratio)", "DEFINED"),
    ("(ii) realization ↔ TateDescentCriterion", "PROVED (given j ≠ 0,1728 and 2,3 ≠ 0)"),
    ("(ii) proof of IsSquare (γ X / γ E_q) from split multiplicative reduction", "MISSING (arithmetic)"),
    ("(iii) TatePointComparison point uniformization", "MISSING (analytic)") ]

theorem descentRows_length : descentRows.length = 5 := rfl

#check tateDescent_iff_square
#check realization_iff_descentCriterion
#check descentRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TateDescentReductionActual
end
