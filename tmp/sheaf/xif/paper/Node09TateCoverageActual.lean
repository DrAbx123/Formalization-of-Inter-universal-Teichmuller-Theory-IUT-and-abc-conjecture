import tmp.sheaf.xif.paper.Node09TateYInversionActual
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationPointMapReduction

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Node09TateCoverageActual

universe u
variable {K : Type u} [NormedField K] [CharZero K]

/-- Coverage residual: every nonsingular affine point is hit by a pole-excluded
parameter.  This is the exact Weierstrass-preparation/Hensel target. -/
def TateCoverageResidual (q : K) : Prop :=
  TateCurve.tateCoordinatesCoverNonzeroPoints q

def Node09TateCoverageStatus : List String :=
  [ "coverage target is the pair-level tateCoordinatesCoverNonzeroPoints; it is equivalent to surjectivity of the quotient point map (TateUniformizationPointMapReduction)",
    "missing analytic lemma: for nonsingular (x,y), solve X(u)=x by Weierstrass preparation/Hensel on the annulus, then select the Y branch; no Hensel/Weierstrass-preparation donor for the actual Lambert series X,Y exists",
    "the Newton-polygon remainder bounds and Laurent expansion are available in Node09TateLaurentExpansionActual / Node09TateNewtonPolygonActual but do not provide existence of a parameter solution",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09TateCoverageActual