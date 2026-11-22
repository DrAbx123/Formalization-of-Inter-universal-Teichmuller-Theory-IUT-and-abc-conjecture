/- A3 / F2.3: `fermatCurveScheme n` (over ℚ) is integral.

  Route: the generic gluing lemma `Scheme.GlueData.glued_isIntegral` reduces integrality of the
  glued curve to integrality of its two charts and of the overlap, plus nonemptiness of all
  pairwise overlaps. The chart/overlap rings are domains over ℚ
  (`Mzk1G1A3ChartFracActual.chartRing_isDomain`, `Mzk1G1A3CurveDomainActual.chartInfRing_isDomain`,
  `_overlapRing_isDomain`), so `Spec` of each is integral (and nonempty). No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveActual
import tmp.sheaf.xif.paper.Mzk1G1FermatTwoChartGluingActual
import tmp.sheaf.xif.paper.Mzk1HullFermatGluingActual
import tmp.sheaf.xif.paper.Mzk1SchemeGluedIntegralActual
import tmp.sheaf.xif.paper.Mzk1G1A3ChartFracActual
import tmp.sheaf.xif.paper.Mzk1G1A3CurveDomainActual
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1A3CurveIntegralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1HullFermatGluingActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3ChartFracActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3CurveDomainActual

variable (n : Nat)

/-- **`fermatCurveScheme n` 整**（ℚ 上，n > 0）。 -/
theorem curve_isIntegral (hn : 0 < n) : IsIntegral (fermatCurveScheme n) := by
  haveI : IsDomain (R n) := chartRing_isDomain n hn
  haveI : IsDomain (R2 n) := chartInfRing_isDomain n hn
  haveI : IsDomain (Overlap0 n) := overlapRing_isDomain n hn
  haveI : ∀ i, IsIntegral ((fermatTwoChartGlueData n).U i) := by
    intro i
    obtain ⟨b⟩ := i
    cases b
    · change IsIntegral (fermatChart0Scheme n)
      infer_instance
    · change IsIntegral (fermatChartInfScheme n)
      infer_instance
  have hne : ∀ i j, Nonempty ((fermatTwoChartGlueData n).V (i, j)) := by
    intro i j
    obtain ⟨bi⟩ := i
    obtain ⟨bj⟩ := j
    cases bi <;> cases bj
    · change Nonempty (fermatChart0Scheme n)
      infer_instance
    · change Nonempty (fermatOverlapScheme n)
      infer_instance
    · change Nonempty (fermatOverlapScheme n)
      infer_instance
    · change Nonempty (fermatChartInfScheme n)
      infer_instance
  have h := Scheme.GlueData.glued_isIntegral (D := fermatTwoChartGlueData n) hne
  simpa [fermatCurveScheme_eq_glued n] using h

#print axioms curve_isIntegral

end LeanFormal.IUT.XiFPaper.Mzk1G1A3CurveIntegralActual