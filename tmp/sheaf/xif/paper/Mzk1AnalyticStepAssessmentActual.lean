/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import TateCurvesTheta.Converse.QuadraticTwist
import Mathlib.Tactic

/-! # Mzk1AnalyticStepAssessmentActual — (ii)/(iii) analytic first steps (A813, qpilot)

Assessment of the two remaining A801 gaps.

**(ii) base-level realization.**  Over a separably closed field, equal `j`-invariants of
two elliptic curves give a variable change (Mathlib `exists_variableChange_of_j_eq`,
re-exported here).  The green source alignment (`SourceTateParameterAlignment`) provides
the base-level j-equality plus a variable change over the algebraic closure.  Hence the
analytic content of (ii) is exactly the *descent* of that variable change from the
algebraic closure to the completion.  Quadratic twists (same j) show that base
j-equality alone does not give a base variable change, so the descent is genuine content,
not a formality.

**(iii) point uniformization.**  `TatePointComparison` asks for a group isomorphism
`(Kbarˣ ⧸ q^ℤ) ≃* Multiplicative (X.baseChange Kbar).AlgebraicClosurePoint` plus Galois
naturality.  The vendor analytic uniformization supplies the quotient side; the model
identification with LeanFormal's `AlgebraicClosurePoint` is the missing analytic theorem.
Formalizable first steps: the quotient side is nonempty (unit class) and the target side
has a point; recorded below as the abstract nonemptiness interface.

No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AnalyticStepAssessmentActual

/-! ### 1. Step (ii): j-equality over a separably closed field -/

theorem realization_over_sepClosed {F : Type*} [Field F] [IsSepClosed F]
    (E E' : WeierstrassCurve F) [E.IsElliptic] [E'.IsElliptic]
    (heq : E.j = E'.j) :
    ∃ C : WeierstrassCurve.VariableChange F, C • E = E' :=
  WeierstrassCurve.exists_variableChange_of_j_eq E E' heq

/-! ### 2. Why descent is genuine: quadratic twists have the same j -/

/-- Quadratic twist preserves the j-invariant (vendor `j_quadraticTwist`). -/
theorem twist_same_j {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic]
    {d : F} (hd : d ≠ 0) (h2 : (2 : F) ≠ 0)
    [(TateCurvesTheta.quadraticTwist W d).IsElliptic] :
    (TateCurvesTheta.quadraticTwist W d).j = W.j :=
  TateCurvesTheta.j_quadraticTwist W hd h2

/-! ### 3. Step (iii): nonemptiness of the two sides of the point comparison -/

/-- The deck-quotient side is nonempty: the class of the unit. -/
theorem deckQuotient_nonempty {K : Type*} [Field K] (q : Kˣ) :
    Nonempty (Kˣ ⧸ Subgroup.zpowers q) :=
  ⟨QuotientGroup.mk 1⟩

/-- A Weierstrass curve has a projective point (the point at infinity). -/
theorem curvePoint_nonempty {F : Type*} [Field F] (W : WeierstrassCurve F) :
    Nonempty W.toProjective.Point :=
  ⟨0⟩

/-! ### 4. Rows -/

def analyticStepRows : List (String × String) :=
  [ ("(ii) separably closed j-equality ⇒ variable change", "PROVED (Mathlib re-export)"),
    ("(ii) base j-equality (green source alignment)", "GREEN (read-only)"),
    ("(ii) descent of variable change closure → completion", "MISSING (analytic/descent)"),
    ("(ii) quadratic twist has same j (base j-equality not sufficient)", "PROVED"),
    ("(iii) deck quotient nonempty", "PROVED"),
    ("(iii) curve point side nonempty", "PROVED"),
    ("(iii) pointEquiv group isomorphism + Galois naturality", "MISSING (analytic uniformization)") ]

theorem analyticStepRows_length : analyticStepRows.length = 7 := rfl

#check realization_over_sepClosed
#check twist_same_j
#check deckQuotient_nonempty
#check analyticStepRows_length

end LeanFormal.IUT.XiFPaper.Mzk1AnalyticStepAssessmentActual
end
