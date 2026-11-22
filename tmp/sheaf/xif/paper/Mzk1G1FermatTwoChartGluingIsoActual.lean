/-
G1-A hull: the two-chart glued Fermat curve with separate overlap schemes and the
overlap isomorphism as transition map (avoids the identity transition map).
-/
import tmp.sheaf.xif.paper.Mzk1HullFermatGluingActual
import tmp.sheaf.xif.paper.Mzk1G1FermatOverlapActual
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingIsoActual
open LeanFormal.IUT.XiFPaper.Mzk1HullFermatGluingActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
/-- The affine chart U0 = Spec A0. -/
abbrev fermatChart0Scheme (n : Nat) : Scheme := Spec (CommRingCat.of (Chart0Ring n))
/-- The affine chart at infinity U1 = Spec A1. -/
abbrev fermatChartInfScheme (n : Nat) : Scheme := Spec (CommRingCat.of (ChartInfRing n))
/-- The overlap D(x) inside the first chart. -/
abbrev fermatOverlap0Scheme (n : Nat) : Scheme := Spec (CommRingCat.of (Overlap0 n))
/-- The overlap D(r) inside the chart at infinity. -/
abbrev fermatOverlapInfScheme (n : Nat) : Scheme := Spec (CommRingCat.of (OverlapInf n))
/-- D(x) -> U0. -/
def fermatOverlap0ToChart0 (n : Nat) : fermatOverlap0Scheme n ⟶ fermatChart0Scheme n :=
  overlapToChart0 n
/-- D(r) -> U1. -/
def fermatOverlapInfToChartInf (n : Nat) : fermatOverlapInfScheme n ⟶ fermatChartInfScheme n :=
  Spec.map (CommRingCat.ofHom (algebraMap (ChartInfRing n) (OverlapInf n)))
instance fermatOverlap0ToChart0_isOpenImmersion (n : Nat) :
    IsOpenImmersion (fermatOverlap0ToChart0 n) :=
  overlapToChart0_isOpenImmersion n
instance fermatOverlapInfToChartInf_isOpenImmersion (n : Nat) :
    IsOpenImmersion (fermatOverlapInfToChartInf n) := by
  show IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap (ChartInfRing n) (OverlapInf n))))
  infer_instance
/-- The two-chart gluing data of the Fermat curve, with the overlap ring equivalence
as transition map. -/
noncomputable abbrev fermatTwoChartGlueDataOfIso (n : Nat) : Scheme.GlueData :=
  twoChartGlueDataOfIso (fermatChart0Scheme n) (fermatChartInfScheme n)
    (fermatOverlap0Scheme n) (fermatOverlapInfScheme n)
    (fermatOverlap0ToChart0 n) (fermatOverlapInfToChartInf n) (overlapSchemeIso n)
    (fermatOverlap0ToChart0_isOpenImmersion n) (fermatOverlapInfToChartInf_isOpenImmersion n)
/-- The glued Fermat curve in the two-overlap model. -/
noncomputable abbrev fermatCurveSchemeIso (n : Nat) : Scheme :=
  (fermatTwoChartGlueDataOfIso n).glued
/-- The index of the first chart. -/
def fermatGlueIdx0 (n : Nat) : (fermatTwoChartGlueDataOfIso n).J := ⟨false⟩
/-- The index of the second chart. -/
def fermatGlueIdx1 (n : Nat) : (fermatTwoChartGlueDataOfIso n).J := ⟨true⟩
/-- U0 -> Y_n. -/
def fermatChart0ToCurveIso (n : Nat) : fermatChart0Scheme n ⟶ fermatCurveSchemeIso n :=
  (fermatTwoChartGlueDataOfIso n).ι (fermatGlueIdx0 n)
/-- U1 -> Y_n. -/
def fermatChartInfToCurveIso (n : Nat) : fermatChartInfScheme n ⟶ fermatCurveSchemeIso n :=
  (fermatTwoChartGlueDataOfIso n).ι (fermatGlueIdx1 n)
instance fermatChart0ToCurveIso_isOpenImmersion (n : Nat) :
    IsOpenImmersion (fermatChart0ToCurveIso n) :=
  (fermatTwoChartGlueDataOfIso n).ι_isOpenImmersion (fermatGlueIdx0 n)
instance fermatChartInfToCurveIso_isOpenImmersion (n : Nat) :
    IsOpenImmersion (fermatChartInfToCurveIso n) :=
  (fermatTwoChartGlueDataOfIso n).ι_isOpenImmersion (fermatGlueIdx1 n)
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoChartGluingIsoActual
