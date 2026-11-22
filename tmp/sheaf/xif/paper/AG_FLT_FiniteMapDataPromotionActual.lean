import tmp.external.ported.flt_th.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

/-!
# AG-FLT finite-map-data promotion (first-class importable; audit component)

COMPONENT, not a paper object.  Named consumers: stepxi GeometricCore finite map
to P1, Lead AG-INFRA-PLAN.  Ported FLT module (Apache-2.0 attribution in header;
module EXIT=0).  This file re-exports the finite-map-data type family as an alias
of the ported structure (no new mathematical content), avoiding a wrapper binder
that previously hit a parser issue.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.AG_FLT_FiniteMapDataPromotionActual

/-- Finite map data for a smooth proper curve over R (ported FLT structure). -/
abbrev promotion_FiniteMapData :=
  @AlgebraicGeometry.SmoothProperCurve.FiniteMapData

end LeanFormal.IUT.XiFPaper.AG_FLT_FiniteMapDataPromotionActual
