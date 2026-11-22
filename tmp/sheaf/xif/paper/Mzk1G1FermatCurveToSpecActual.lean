/-
G1-A: the structure morphism Y_n -> Spec Q of the glued Fermat curve.

Both affine charts are Q-algebras, hence carry structure maps to Spec Q; they agree on the
overlap (both are Spec.map of the Q-algebra structure of the overlap ring), so emmy's
assembler fermatCurveGlueMorphism produces the structure morphism of Y_n.  This is the
input for IsProper(Y_n) (IsProper of pi followed by the structure map of P^1). -/
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveActual
import tmp.sheaf.xif.paper.Mzk1G1PsiXiActual
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveToSpecActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiXiActual
open LeanFormal.IUT.XiFPaper.Mzk1GlueMorphismActual
/-- Structure map of the first chart to Spec Q. -/
def fermatChart0ToSpec (n : Nat) : fermatChart0Scheme n ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (Chart0Ring n)))
/-- Structure map of the chart at infinity to Spec Q. -/
def fermatChartInfToSpec (n : Nat) : fermatChartInfScheme n ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (ChartInfRing n)))
/-- The two chart structure maps agree on the overlap. -/
theorem fermatOverlapToSpec_compat (n : Nat) :
    overlapToChart0 n ≫ fermatChart0ToSpec n =
      overlapToChartInf n ≫ fermatChartInfToSpec n := by
  have hL' : ((algebraMap (Chart0Ring n) (Overlap0 n)).comp
      (algebraMap ℚ (Chart0Ring n))) = algebraMap ℚ (Overlap0 n) := RingHom.ext_rat _ _
  have hR' : (((beta n).comp (algebraMap (ChartInfRing n) (OverlapInf n))).comp
      (algebraMap ℚ (ChartInfRing n))) = algebraMap ℚ (Overlap0 n) := RingHom.ext_rat _ _
  rw [overlapToChart0, fermatChart0ToSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hL']
  rw [overlapToChartInf, fermatChartInfToSpec,
    show (overlapSchemeIso n).hom = overlapSpecMap01 n from rfl, overlapSpecMap01,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    hR']
/-- The structure morphism Y_n -> Spec Q. -/
noncomputable def fermatCurveToSpec (n : Nat) :
    fermatCurveScheme n ⟶ Spec (CommRingCat.of ℚ) :=
  fermatCurveGlueMorphism n (fermatChart0ToSpec n) (fermatChartInfToSpec n)
    (fermatOverlapToSpec_compat n)
/-- The structure morphism restricts to the first chart structure map. -/
theorem fermatCurveToSpec_ι0 (n : Nat) :
    fermatChart0ToCurve n ≫ fermatCurveToSpec n = fermatChart0ToSpec n := by
  unfold fermatCurveToSpec fermatCurveGlueMorphism
  exact glueMorphism_ι (D := fermatTwoChartGlueData n) _ _ (ULift.up false)
/-- The structure morphism restricts to the second chart structure map. -/
theorem fermatCurveToSpec_ι1 (n : Nat) :
    fermatChartInfToCurve n ≫ fermatCurveToSpec n = fermatChartInfToSpec n := by
  unfold fermatCurveToSpec fermatCurveGlueMorphism
  exact glueMorphism_ι (D := fermatTwoChartGlueData n) _ _ (ULift.up true)
#print axioms fermatOverlapToSpec_compat
#print axioms fermatCurveToSpec_ι0
#print axioms fermatCurveToSpec_ι1
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveToSpecActual
