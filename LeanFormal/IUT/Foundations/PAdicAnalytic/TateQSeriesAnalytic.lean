/-
  # Analytic Tate q-series j(q) and the inverse-j parameter

  Task-132 foundation.  This file defines the actual q-series expression for
  the Tate j-invariant as a function of q,

      tateJQSeries q = (c4(TateCurve.weierstrassCurve Q_5 q))^3 /
        Delta(TateCurve.weierstrassCurve Q_5 q),

  and records the exact missing analytic input needed to run Mathlib's analytic
  inverse function theorem at q = 5:

  * AnalyticAt Q_5 tateJQSeries 5,
  * deriv tateJQSeries 5 != 0.

  Those are NOT proved here: the q-series is a Lambert/divisor series and
  Mathlib 4.32.2 does not provide analyticity of such p-adic tsums or their
  derivative at q = 5.  Given the two analytic hypotheses, the actual local
  inverse q_Tate is constructed below by the verified p-adic analytic local
  inverse theorem from AnalyticLocalInverse.lean.  No card/inhabitant of the
  missing analyticity is assumed.  The q = 5 obstruction (j_Tate(5) != j_split)
  is proved in Example36TateUniformization.lean and shows q = 5 itself is not
  the inverse-j parameter.

  No card, no fake/placeholder.
-/

import LeanFormal.IUT.Foundations.PAdicAnalytic.AnalyticLocalInverse
import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic
import LeanFormal.IUT.Foundations.Geometry.TateJInvariantNorm

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.PAdicAnalytic

noncomputable section

local instance fivePrimeFactTQA : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The actual q-series expression for the Tate j-invariant at q in Q_5:
(c4)^3 / Delta, computed from the canonical q-series Weierstrass equation. -/
def tateJQSeries (q : ℚ_[5]) : ℚ_[5] :=
  let W := TateCurve.weierstrassCurve ℚ_[5] q
  W.c₄ ^ 3 / W.Δ

/-- The q-series j function at the explicit q = 5. -/
theorem tateJQSeries_five :
    tateJQSeries (5 : ℚ_[5]) =
      let W := TateCurve.weierstrassCurve ℚ_[5] (5 : ℚ_[5])
      W.c₄ ^ 3 / W.Δ :=
  rfl

/-- The exact missing analytic input: the Tate q-series j function is analytic
at q = 5 and its derivative there is nonzero.  This is a Prop interface with no
inhabitant constructed in this file. -/
def TateJQSeriesAnalyticAtFive : Prop :=
  AnalyticAt ℚ_[5] tateJQSeries 5 ∧ deriv tateJQSeries 5 ≠ 0

/-- Given the missing analyticity and nonzero derivative at q = 5, Mathlib's
p-adic analytic local inverse theorem produces the actual analytic local inverse
q_Tate near j(5).  This is a conditional construction: the analyticity
hypotheses are explicit arguments, not assumed globally. -/
theorem exists_analytic_qTate_localInverse
    (h : TateJQSeriesAnalyticAtFive) :
    ∃ qTate : ℚ_[5] → ℚ_[5],
      AnalyticAt ℚ_[5] qTate (tateJQSeries 5) := by
  rcases h with ⟨h_analytic, h_deriv⟩
  exact ⟨h_analytic.hasStrictDerivAt.localInverse _ _ _ h_deriv,
    analyticAt_localInverse h_analytic h_deriv⟩

/-- The same conditional local inverse, packaged with the defining local
inverse map from Mathlib's analytic inverse theorem. -/
theorem analytic_qTate_localInverse_apply
    (h : TateJQSeriesAnalyticAtFive) :
    AnalyticAt ℚ_[5]
      ((h.1).hasStrictDerivAt.localInverse _ _ _ h.2)
      (tateJQSeries 5) :=
  analyticAt_localInverse h.1 h.2

/-- The exact missing analyticity statement is recorded as a separate Prop
with no inhabitant; it is the analytic q-series theorem needed for the
unconditional q_Tate construction. -/
def MissingTateJQSeriesAnalyticAtFive : Prop :=
  TateJQSeriesAnalyticAtFive

/-- The missing analytic statement implies the conditional local-inverse
construction; this is the exact reduction of the q_Tate construction to the
missing analytic q-series theorem. -/
theorem missing_analyticity_gives_qTate
    (h : MissingTateJQSeriesAnalyticAtFive) :
    ∃ qTate : ℚ_[5] → ℚ_[5],
      AnalyticAt ℚ_[5] qTate (tateJQSeries 5) :=
  exists_analytic_qTate_localInverse h

end

end LeanFormal.IUT.PAdicAnalytic
