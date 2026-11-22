/-
G1-A canonical shared export: the Fermat curve Y_n as the real two-chart gluing.

This is the canonical Y_n of route §2.1 (Scheme.GlueData.glued of the two affine charts
glued along D(x) = D(r)); downstream lanes (G-B, G-C, H-T) should import this file.
The accepted closed-subscheme model Mzk1G1FermatProjClosedSubscheme4Actual.fermatCurveScheme
remains the proper/closed transport target; the isomorphism between the two models is the
next item on this lane (not yet proved), together with pi : Y_n -> P^1.
-/
import tmp.sheaf.xif.paper.Mzk1G1FermatTwoChartGluingActual
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
/-- The canonical Fermat curve Y_n, as the glued scheme of the two affine charts. -/
abbrev fermatCurveScheme (n : Nat) : Scheme :=
  Mzk1G1FermatTwoChartGluingActual.fermatCurveScheme n
/-- The first affine chart U0 = Spec A0 of Y_n. -/
abbrev fermatChart0Scheme (n : Nat) : Scheme :=
  Mzk1G1FermatTwoChartGluingActual.fermatChart0Scheme n
/-- The affine chart at infinity U1 = Spec A1 of Y_n. -/
abbrev fermatChartInfScheme (n : Nat) : Scheme :=
  Mzk1G1FermatTwoChartGluingActual.fermatChartInfScheme n
/-- The common overlap D(x) = D(r). -/
abbrev fermatOverlapScheme (n : Nat) : Scheme :=
  Mzk1G1FermatTwoChartGluingActual.fermatOverlapScheme n
/-- The open immersion U0 -> Y_n. -/
abbrev fermatChart0ToCurve (n : Nat) : fermatChart0Scheme n ⟶ fermatCurveScheme n :=
  Mzk1G1FermatTwoChartGluingActual.fermatChart0ToCurve n
/-- The open immersion U1 -> Y_n. -/
abbrev fermatChartInfToCurve (n : Nat) : fermatChartInfScheme n ⟶ fermatCurveScheme n :=
  Mzk1G1FermatTwoChartGluingActual.fermatChartInfToCurve n
/-- The two-chart gluing data of Y_n (its Scheme.GlueData). -/
abbrev fermatTwoChartGlueData (n : Nat) : Scheme.GlueData :=
  Mzk1G1FermatTwoChartGluingActual.fermatTwoChartGlueData n
theorem fermatCurveScheme_eq_glued (n : Nat) :
    fermatCurveScheme n = (fermatTwoChartGlueData n).glued := rfl
theorem fermatChart0ToCurve_isOpenImmersion (n : Nat) :
    IsOpenImmersion (fermatChart0ToCurve n) :=
  Mzk1G1FermatTwoChartGluingActual.fermatChart0ToCurve_isOpenImmersion n
theorem fermatChartInfToCurve_isOpenImmersion (n : Nat) :
    IsOpenImmersion (fermatChartInfToCurve n) :=
  Mzk1G1FermatTwoChartGluingActual.fermatChartInfToCurve_isOpenImmersion n
/-- The open cover of Y_n by its two charts, as an OpenCover of the glued scheme. -/
def fermatCurveOpenCover (n : Nat) : (fermatCurveScheme n).OpenCover :=
  (fermatTwoChartGlueData n).openCover
#print axioms fermatCurveScheme_eq_glued
#print axioms fermatChart0ToCurve_isOpenImmersion
#print axioms fermatChartInfToCurve_isOpenImmersion
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
