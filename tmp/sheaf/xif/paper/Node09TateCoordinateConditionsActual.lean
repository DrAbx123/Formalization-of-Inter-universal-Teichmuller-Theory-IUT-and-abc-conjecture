import LeanFormal.IUT.Foundations.Geometry.TateUniformizationPointMapReduction

noncomputable section
open LeanFormal.IUT.TateCurve

namespace LeanFormal.IUT.XiFPaper.Node09TateCoordinateConditionsActual

universe u

variable {K : Type u} [NormedField K] [CharZero K] {q : K}

/-- §5.2 orbit-separation residual: equal X- and Y-coordinates of two
pole-excluded parameters force the same q^Z-orbit. -/
def TateOrbitSeparationResidual (q : K) : Prop :=
  tatePairCoordinatesSeparateOrbits q

/-- §5.2 coverage residual: every nonsingular affine point is the coordinate
pair of a pole-excluded parameter. -/
def TateCoordinateCoverageResidual (q : K) : Prop :=
  tateCoordinatesCoverNonzeroPoints q

/-- The point-map gap is exactly orbit separation plus coverage. -/
theorem tatePointMapGap_iff_coordinateResiduals
    (q : K) (parameterNeZero : q ≠ 0) (hdata : TateWeierstrassPointData q) :
    TateUniformizationPointMapGap q parameterNeZero hdata ↔
      TateOrbitSeparationResidual q ∧ TateCoordinateCoverageResidual q :=
  tateUniformizationPointMapGap_iff_pairConditions q parameterNeZero hdata

/-- Projection: the gap gives actual orbit separation. -/
theorem tateOrbitSeparation_of_gap
    (q : K) (parameterNeZero : q ≠ 0) (hdata : TateWeierstrassPointData q)
    (hgap : TateUniformizationPointMapGap q parameterNeZero hdata) :
    TateOrbitSeparationResidual q :=
  (tatePointMapGap_iff_coordinateResiduals q parameterNeZero hdata).mp hgap |>.1

/-- Projection: the gap gives actual coverage. -/
theorem tateCoordinateCoverage_of_gap
    (q : K) (parameterNeZero : q ≠ 0) (hdata : TateWeierstrassPointData q)
    (hgap : TateUniformizationPointMapGap q parameterNeZero hdata) :
    TateCoordinateCoverageResidual q :=
  (tatePointMapGap_iff_coordinateResiduals q parameterNeZero hdata).mp hgap |>.2

/-- Exact status of the §5.2 coordinate conditions. -/
def Node09TateCoordinateConditionsStatus : List String :=
  [ "available: tateUniformizationPointMapGap_iff_pairConditions reduces the point gap to tatePairCoordinatesSeparateOrbits and tateCoordinatesCoverNonzeroPoints; both residuals are now named TateOrbitSeparationResidual / TateCoordinateCoverageResidual",
    "available forward direction: tateWeierstrassX_eq_of_orbitRel and tateWeierstrassY_eq_of_orbitRel prove that q^Z-related parameters have equal coordinates; tateQuotientPoint_ne_zero proves the parametrization omits only the point at infinity",
    "FIRST MISSING analytic lemma for orbit separation: the converse Laurent/annulus analysis. Needed: q-Laurent expansion of tateWeierstrassX/Y on a fundamental annulus, pole order 2 of X at the origin, zero-count/Newton-polygon argument showing X(u)=x has exactly the two branches u and u^{-1} modulo q^Z, and the Y inversion formula selecting matching branches. No such annulus/Laurent/Newton-polygon lemma exists in the tree",
    "FIRST MISSING analytic lemma for coverage: for a nonsingular affine point (x,y), solve tateWeierstrassX q u = x by the same zero-count/Newton-polygon or Weierstrass preparation/Hensel argument, then choose the branch with Y(u)=y. No Hensel/Weierstrass-preparation donor for the actual Lambert-series X,Y exists",
    "the existing reduction file proves only the logical equivalence of the gap with the pair conditions; it explicitly does not prove either pair condition, so there is no fake construction here",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09TateCoordinateConditionsActual
