import tmp.external.ported.flt_th.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import tmp.sheaf.xif.paper.GeomCore01StatementActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# GeomCore02: GeometricCore input wiring (data/wiring only; assembly GATED by Lead)

Maps [Mzk1] Theorem 2.5 (GeometricCore) inputs to the canonical assets now green:
* finite map to P1: canonical ported module
  tmp.external.ported.flt_th.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
  (green EXIT=0; structure AlgebraicGeometry.SmoothProperCurve.FiniteMapData; the
  non-canonical wrapper was abandoned per qpilot, import the ported module directly);
* RR rows + two complete RR reductions: AG_FLT_RiemannRochPromotionActual (CITABLE 8);
* Cech H0/H1: AG_FLT_CechPromotionActual (CITABLE 5) -> AG05CechActual;
* canonical divisor/genus: AG_FLT_CanonicalDivisorPromotionActual (CITABLE 3) ->
  AG10CanonicalDivisorGenusActual;
* basepoint-free pencil: geometric input from RR + finite map (statement layer
  GeomCore01StatementActual.BasepointFreePencil);
* Mzk1 Thm 2.5 itself: class-D paper-input (Mzk1Theorem25StatementActual placeholder
  NOT consumed).
Lead gate: GeometricCore assembly remains gated until (a)+(b) close; this file does
NOT claim assembly.  Belyi existence (TauCeti tauceti_rr Belyi/Basic) still porting.
**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.GeomCore02WiringActual

/-- Wiring rows: (GeometricCore input, canonical asset, status). -/
def geomCoreInputWiring : List (String × String × String) :=
  [ ("finite map to P1 data", "tmp.external.ported.flt_th.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData (ported EXIT=0)", "A (asset green; import directly)"),
    ("RR rows + reductions", "AG_FLT_RiemannRochPromotionActual (CITABLE 8; two COMPLETE reductions)", "A (green)"),
    ("Cech H0/H1", "AG_FLT_CechPromotionActual (CITABLE 5) -> AG05CechActual (CITABLE 11)", "A (green)"),
    ("canonical divisor / genus", "AG_FLT_CanonicalDivisorPromotionActual (CITABLE 3) -> AG10CanonicalDivisorGenusActual", "A (green)"),
    ("basepoint-free pencil", "GeomCore01StatementActual.BasepointFreePencil (statement)", "statement layer; construction from RR+finite map gated"),
    ("Belyi existence", "TauCeti tauceti_rr Belyi/Basic (porting; dependency drift)", "PENDING"),
    ("Mzk1 Thm 2.5", "Mzk1Theorem25StatementActual (placeholder True; precise statement required)", "class-D paper-input; NOT consumed"),
    ("GeometricCore assembly", "GeomCore01StatementActual.GeometricCoreData + A-class assets above", "GATED by Lead until (a)+(b) close") ]

/-- Non-canonical wrapper record (per qpilot): use ported module import directly. -/
def geomCoreWrapperPolicy : List (String × String) :=
  [ ("FiniteMapData", "import tmp.external.ported.flt_th.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData directly; wrapper abandoned"),
    ("RR/Serde", "consume AG_FLT_RiemannRochPromotionActual"),
    ("Cech", "consume AG_FLT_CechPromotionActual"),
    ("canonical divisor/genus", "consume AG_FLT_CanonicalDivisorPromotionActual") ]

end LeanFormal.IUT.XiFPaper.GeomCore02WiringActual
