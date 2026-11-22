/-
G1-A hull: the real two-chart glued Fermat curve Y_n.

U0 = Spec A0, A0 = Q[X0,X1]/(X0^n + X1^n - 1)          (the affine chart x != 0)
U1 = Spec A1, A1 = Q[X0,X1]/(1 + X0^n - X1^n)          (the chart at infinity: X0 = s, X1 = r)
The two charts are glued along the common overlap D(x) = D(r) using the real overlap
ring equivalence of Mzk1G1FermatOverlapActual (r = x^{-1}, s = y x^{-1}, mutually inverse).
The glued scheme is an honest Scheme.GlueData.glued with its two chart open immersions
and the gluing cocycle; it is the actual Y_n from which pi : Y_n -> P^1 is built.
-/
import tmp.sheaf.xif.paper.Mzk1HullFermatGluingActual
import tmp.sheaf.xif.paper.Mzk1G1FermatOverlapActual
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual
open LeanFormal.IUT.XiFPaper.Mzk1HullFermatGluingActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
/-- The affine chart U0 = Spec A0. -/
abbrev fermatChart0Scheme (n : Nat) : Scheme := Spec (CommRingCat.of (Chart0Ring n))
/-- The affine chart at infinity U1 = Spec A1. -/
abbrev fermatChartInfScheme (n : Nat) : Scheme := Spec (CommRingCat.of (ChartInfRing n))
/-- The common overlap D(x) = D(r), presented by the chart-0 localization. -/
abbrev fermatOverlapScheme (n : Nat) : Scheme := Spec (CommRingCat.of (Overlap0 n))
/-- The real two-chart gluing data of the Fermat curve. -/
noncomputable abbrev fermatTwoChartGlueData (n : Nat) : Scheme.GlueData :=
  twoChartGlueData (fermatChart0Scheme n) (fermatChartInfScheme n) (fermatOverlapScheme n)
    (overlapToChart0 n) (overlapToChartInf n)
    (overlapToChart0_isOpenImmersion n) (overlapToChartInf_isOpenImmersion n)
/-- The Fermat curve Y_n, as the glued scheme of the two affine charts. -/
noncomputable abbrev fermatCurveScheme (n : Nat) : Scheme := (fermatTwoChartGlueData n).glued
theorem fermatCurveScheme_def (n : Nat) :
    fermatCurveScheme n = (fermatTwoChartGlueData n).glued := rfl
/-- The index of the first chart, in the index type of the gluing data. -/
def fermatIdx0 (n : Nat) : (fermatTwoChartGlueData n).J := ⟨false⟩
/-- The index of the second chart, in the index type of the gluing data. -/
def fermatIdx1 (n : Nat) : (fermatTwoChartGlueData n).J := ⟨true⟩
/-- The open immersion of the first chart into Y_n. -/
def fermatChart0ToCurve (n : Nat) : fermatChart0Scheme n ⟶ fermatCurveScheme n :=
  (fermatTwoChartGlueData n).ι (fermatIdx0 n)
/-- The open immersion of the second chart into Y_n. -/
def fermatChartInfToCurve (n : Nat) : fermatChartInfScheme n ⟶ fermatCurveScheme n :=
  (fermatTwoChartGlueData n).ι (fermatIdx1 n)
instance fermatChart0ToCurve_isOpenImmersion (n : Nat) :
    IsOpenImmersion (fermatChart0ToCurve n) :=
  (fermatTwoChartGlueData n).ι_isOpenImmersion (fermatIdx0 n)
instance fermatChartInfToCurve_isOpenImmersion (n : Nat) :
    IsOpenImmersion (fermatChartInfToCurve n) :=
  (fermatTwoChartGlueData n).ι_isOpenImmersion (fermatIdx1 n)
/-- The overlap sits in Y_n through the first chart. -/
def fermatOverlapToCurve (n : Nat) : fermatOverlapScheme n ⟶ fermatCurveScheme n :=
  overlapToChart0 n ≫ fermatChart0ToCurve n
/- TECHNICAL NOTE (for the next batch on pi).  The user-facing cocycle equation
     overlapToChart0 n ≫ fermatChart0ToCurve n = overlapToChartInf n ≫ fermatChartInfToCurve n
is the (false,true) instance of Scheme.GlueData.glue_condition with t = identity, and it is
what the pi gluing needs.  Deriving it from glue_condition currently fails in the final
rewrite by Category.id_comp: after substituting t = 𝟙 _ the term 𝟙 (V (i,j)) ≫ f is not
recognised as a composable pair because the defeq check V (i,j) = V (j,i) does not fire
(the two are equal only after reducing the ULift index projections inside the match that
defines twoChartV).  Fixes to try: (a) prove in the generic file a two-index cocycle lemma
stated with the V-equality hypothesis and eqToHom; (b) in twoChartV, use a definition whose
value on (false,true) and (true,false) is syntactically the same term without match on the
pair; (c) prove the equation by transporting chart maps through the pullback iso instead of
rewriting inside the glue_condition equation.  The cocycle itself is already proved inside
the GluingData (t_fac/cocycle fields), so this is only the user-level restatement. -/
#print axioms fermatChart0ToCurve_isOpenImmersion
#print axioms fermatCurveScheme_def
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingActual
