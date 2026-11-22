namespace LeanFormal.IUT.XiFPaper.Node09TateAnalyticMathlibActual

/-- Usable Mathlib 4.32.2 lemmas for the N1 analyticity blocker, and the exact
first missing local lemma.  Documentation only. -/
def Node09TateAnalyticMathlib : List String :=
  [ "Mathlib usable 1: FormalMultilinearSeries.ofScalars (Mathlib/Analysis/Analytic/OfScalars.lean:38) builds a formal multilinear series from a scalar coefficient sequence; ofScalars_apply_eq (:122) gives (ofScalars c n) (fun _ => x) = c n • x^n and ofScalars_sum_eq (:134) identifies its sum with tsum n, c n • x^n",
    "Mathlib usable 2: FormalMultilinearSeries.hasFPowerSeriesOnBall (Mathlib/Analysis/Analytic/Basic.lean:1074) states HasFPowerSeriesOnBall p.sum p 0 p.radius",
    "Mathlib usable 3: FormalMultilinearSeries.le_radius_of_bound (Mathlib/Analysis/Analytic/ConvergenceRadius.lean:97) and le_radius_of_bound_nnreal (:102): a bound ||p n|| * r^n <= C implies r <= p.radius; with bounded coefficients (||p n|| <= 1) this gives radius >= 1",
    "Mathlib usable 4: FormalMultilinearSeries.hasFPowerSeriesOnBall_changeOrigin (Mathlib/Analysis/Analytic/ChangeOrigin.lean:252), changeOrigin_eval (:258) and analyticAt_changeOrigin (:297): once 5 lies inside the radius, change origin from 0 to 5 and translate analyticity back to p.sum at 5",
    "Mathlib usable 5: AnalyticAt.div (Mathlib/Analysis/Analytic/Constructions.lean:1115): analyticity of c4^3 and Delta at 5 plus Delta(5) != 0 gives analyticity of the quotient tateJQSeries",
    "first missing local lemma A: coefficient norm bound for the integral series C4K^3 and DK over Z_5, e.g. forall n, ||(((C4K^3).coeff n : PadicInt 5) : Q_5)|| <= 1 and same for DK; TateQSeriesCoefficients/TateQSeriesEval provide the formal series and evaluation identities but not this boundedness for the powers/quotient used in tateJQSeries",
    "first missing local lemma B: identification of the ofScalars sum at q with TateCurve c4(q)^3 and Delta(q) (TateQSeriesEval proves padicPowerSeriesEval is multiplicative and evaluates C4K/DK, which supplies the ingredients, but the exact pointwise equality of the ofScalars series with tateJQSeries numerator/denominator still has to be assembled)",
    "independent missing input: deriv tateJQSeries 5 != 0; no derivative computation of the infinite q-series quotient is available in the tree",
    "no fake and no new axiom" ]

end LeanFormal.IUT.XiFPaper.Node09TateAnalyticMathlibActual
