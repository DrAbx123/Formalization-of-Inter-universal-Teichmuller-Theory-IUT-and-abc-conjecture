namespace LeanFormal.IUT.XiFPaper.Node09TateAnalyticBlockerActual

/-- Exact blocker for TateJQSeriesAnalyticAtFive, after inspecting the q-series
definitions.  Documentation only. -/
def Node09TateAnalyticBlocker : List String :=
  [ "tateJQSeries is NOT rational in q: TateCurve.a4 and a6 are infinite Lambert series (TateCurve.lambertSeries, sum n^k q^n/(1-q^n)), so c4^3 and Delta are polynomial expressions in those infinite series; the ratio is an infinite series, not a rational function",
    "first missing analytic lemma: AnalyticAt Q_5 (fun q => (TateCurve.weierstrassCurve Q_5 q).c₄ ^ 3) 5 and AnalyticAt Q_5 (fun q => (TateCurve.weierstrassCurve Q_5 q).Δ) 5; equivalently analyticity at q=5 of the p-adic power-series evaluation of the integral series C4K^3 / DK (TateQSeriesCoefficients / TateQSeriesEval)",
    "no donor: TateQSeriesCoefficients proves the coefficient/Lambert reindex and integrality of coefficients; TateQSeriesEval proves the actual p-adic evaluation map is additive/multiplicative and identifies it with c4,c6,Delta,H; neither proves HasFPowerSeriesAt/AnalyticAt for the evaluation tsum at an interior point; TateQSeriesAnalytic explicitly records AnalyticAt Q_5 tateJQSeries 5 as missing",
    "second missing input: deriv tateJQSeries 5 != 0; no derivative computation of the q-series quotient is available, and q=5 is not the inverse-j parameter (Example36TateUniformization shows j_Tate(5) != j_split)",
    "conditional construction already exists: TateQSeriesAnalytic.exists_analytic_qTate_localInverse takes TateJQSeriesAnalyticAtFive as an explicit hypothesis and produces the local inverse; no inhabitant of the hypothesis is constructed",
    "analyticAt reduction note: if analyticity of the numerator c4^3 and denominator Delta at q=5 were supplied, AnalyticAt.div would give analyticity of tateJQSeries at 5 once Delta(5) != 0; that reduction is not formalized here because the two series analyticity hypotheses are exactly the missing lemmas",
    "no fake and no new axiom" ]

end LeanFormal.IUT.XiFPaper.Node09TateAnalyticBlockerActual
