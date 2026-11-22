import tmp.sheaf.xif.paper.AG_FLT_FiniteMapDataPromotionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# AG15: canonical FiniteMapData consumer (A-class alias; qpilot promotion)

STEP 0 prior-art (reuse, no re-proof): qpilot AG_FLT_FiniteMapDataPromotionActual
(CITABLE 1) is the clean alias of the ported
AlgebraicGeometry.SmoothProperCurve.FiniteMapData (ported flt_th module EXIT=0;
Apache-2.0 attribution retained).  This file is the AG-layer consumer record; the
FiniteMapData asset is the geometric input of [Mzk1] GeometricCore (finite map to P1)
and of the Belyi layer.  No axiom added.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.AG15FiniteMapCanonicalActual

/-- A-class reuse record: canonical FiniteMapData promotion + consumers. -/
def ag15Reuse : List (String × String × String) :=
  [ ("canonical FiniteMapData alias", "AG_FLT_FiniteMapDataPromotionActual (CITABLE 1; alias of ported flt_th SmoothProperCurve.FiniteMapData)", "A (green; canonical import for GeometricCore)"),
    ("ported module", "tmp.external.ported.flt_th.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData (EXIT=0)", "A (asset; import directly)"),
    ("GeometricCore consumers", "GeomCore02WiringActual (input wiring); GeomCore03AssemblyActual (gated assembly); Mzk1 GeometricCore real-structure skeleton", "A (reuse)"),
    ("wrapper policy", "use canonical alias/module directly; non-canonical wrapper abandoned (qpilot)", "policy") ]

/-- GeometricCore input wiring pointers (data). -/
def ag15GeomCorePointers : List (String × String) :=
  [ ("finite map", "canonical FiniteMapData (AG_FLT_FiniteMapDataPromotionActual) or ported flt_th module"),
    ("pencil/basepoint-free", "GeomCore01StatementActual.BasepointFreePencil (statement layer; construction gated)"),
    ("RR/Serde/Cech", "AG14ProvedTheoremsConsumerActual + AG_FLT_RiemannRochPromotionActual + AG05/AG06b"),
    ("assembly", "GeomCore03AssemblyActual (GATED; no closure claim)") ]

end LeanFormal.IUT.XiFPaper.AG15FiniteMapCanonicalActual
