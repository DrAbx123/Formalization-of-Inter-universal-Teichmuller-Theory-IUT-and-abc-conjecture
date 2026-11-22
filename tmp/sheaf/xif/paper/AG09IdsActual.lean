/-!
# AG09: AG05/AG06/AG06b/AG07/AG08/GeomCore ids (data only; pins 14041)

Gate (e) status ids:
* INDEX.AG.cech -> AG05CechActual: agCechDiff/agCechH0/agCechH1, ag_cechH0_eq,
  ag_cechH1_eq, ag_mem_cechH0_iff, ag_cechH0Equiv (H0 = L(D) on two-chart covers),
  ag_riemannRochSpace_le_lSpaceOn, ag_lSpaceOn_mono, ag_lSpaceOn_union, agCechReuse
  (imports canonical AG_FLT_CechPromotionActual / AG_FLT_CechSectionsActual /
  AG_FLT_TwoChartCechActual / AG_FLT_PromotionActual; Mathlib SheafCohomology).
* INDEX.AG.line-bundle -> AG06LineBundleActual: ag_place_deg_nonneg,
  ag_divisor_degree_add/zero, ag_mem_degZero_iff, ag_isPrincipal_iff_mem,
  ag_ell_nonneg, ag_lSpace_mono, ag_adeleBdd_mono, agLineBundleReuse.
* INDEX.AG.RR-Serde-interface -> AG06bRRInterfaceActual: AGRiemannRochInterface,
  agRRCanonicalAssets, agRRStatusHonesty (canonical assets ASSUMED COMPLETE per Lead).
* INDEX.AG.mathlib-coverage -> AG07MathlibCoverageActual.mathlibCoverage.
* INDEX.AG.proof-status -> AG08ProofStatusTableActual.agProofStatus.
* INDEX.GEOMCORE.statement -> GeomCore01StatementActual: BasepointFreePencil,
  FiniteMapToP1, RamificationData, GeometricCoreData, GeomCorePaperComponents
  ([Mzk1] Thm 2.5 statement-only; assembly gated).
DEPRECATED/not counted: stepxiAGRRFinishActual (duplicate FLT port), AG05CechPortedActual
(temporary ported-flt Čech path, replaced by canonical qpilot promotion imports).
**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.AG09IdsActual

/-- AG gate ids: (index id, declarations, file). -/
def agGateIds : List (String × String × String) :=
  [ ("INDEX.AG.cech", "agCechDiff, agCechH0, agCechH1, ag_cechH0_eq, ag_cechH1_eq, ag_mem_cechH0_iff, ag_cechH0Equiv, ag_riemannRochSpace_le_lSpaceOn, ag_lSpaceOn_mono, ag_lSpaceOn_union, agCechReuse", "AG05CechActual.lean"),
    ("INDEX.AG.line-bundle", "ag_place_deg_nonneg, ag_divisor_degree_add, ag_divisor_degree_zero, ag_mem_degZero_iff, ag_isPrincipal_iff_mem, ag_ell_nonneg, ag_lSpace_mono, ag_adeleBdd_mono, agLineBundleReuse", "AG06LineBundleActual.lean"),
    ("INDEX.AG.RR-Serde-interface", "AGRiemannRochInterface, agRRCanonicalAssets, agRRStatusHonesty", "AG06bRRInterfaceActual.lean"),
    ("INDEX.AG.mathlib-coverage", "mathlibCoverage", "AG07MathlibCoverageActual.lean"),
    ("INDEX.AG.proof-status", "agProofStatus", "AG08ProofStatusTableActual.lean"),
    ("INDEX.GEOMCORE.statement", "BasepointFreePencil, FiniteMapToP1, RamificationData, GeometricCoreData, GeomCorePaperComponents", "GeomCore01StatementActual.lean") ]

end LeanFormal.IUT.XiFPaper.AG09IdsActual
