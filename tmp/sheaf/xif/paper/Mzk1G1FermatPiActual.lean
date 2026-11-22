/-
G1-A: the actual projection pi : Y_n -> P^1, with lambda = x^n / t = r^n.

Y_n is the canonical glued Fermat curve (Mzk1G1FermatCurveActual.fermatCurveScheme) and
P^1 is the canonical glued projective line (Mzk1G1ProjectiveLineGluedActual).  The two
chart maps are
    piChart0  = chartMorphism0  (x0^n)  :  U0 = Spec A0  -> P^1   (lambda = x^n),
    piChartInf = chartMorphismInf (r1^n) :  U1 = Spec A1  -> P^1   (t = r^n),
and they agree on the common overlap by the P^1 transition lemma (fermatPiOverlap_condition:
on the overlap x^n is a unit and t = lambda^{-1} carries x^n to r^n).  The glued morphism is
produced by emmy's shared assembler fermatCurveGlueMorphism (Mzk1G1PsiXiActual).
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiXiActual
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiXiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLinePiOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1GlueMorphismActual
/-- The chart-0 map U0 -> P^1, with lambda = x^n. -/
def piChart0 (n : Nat) : fermatChart0Scheme n ⟶ projectiveLineGlued :=
  chartMorphism0 (R := Chart0Ring n) (x0 n ^ n)
/-- The chart-infinity map U1 -> P^1, with t = r^n. -/
def piChartInf (n : Nat) : fermatChartInfScheme n ⟶ projectiveLineGlued :=
  chartMorphismInf (R := ChartInfRing n) (r1 n ^ n)
/-- The actual projection pi : Y_n -> P^1. -/
noncomputable def pi (n : Nat) : fermatCurveScheme n ⟶ projectiveLineGlued :=
  fermatCurveGlueMorphism n (piChart0 n) (piChartInf n) (fermatPiOverlap_condition n)
/-- The restriction of pi to the first chart is lambda = x^n. -/
theorem pi_ι0 (n : Nat) : fermatChart0ToCurve n ≫ pi n = piChart0 n := by
  unfold pi fermatCurveGlueMorphism piChart0 piChartInf
  exact glueMorphism_ι (D := fermatTwoChartGlueData n) _ _ (ULift.up false)
/-- The restriction of pi to the chart at infinity is t = r^n. -/
theorem pi_ι1 (n : Nat) : fermatChartInfToCurve n ≫ pi n = piChartInf n := by
  unfold pi fermatCurveGlueMorphism piChart0 piChartInf
  exact glueMorphism_ι (D := fermatTwoChartGlueData n) _ _ (ULift.up true)
#print axioms pi_ι0
#print axioms pi_ι1
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiActual
