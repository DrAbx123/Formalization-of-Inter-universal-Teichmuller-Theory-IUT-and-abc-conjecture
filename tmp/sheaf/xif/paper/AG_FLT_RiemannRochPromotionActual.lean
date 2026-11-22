import tmp.external.ported.flt.Definitions.Def_AlgebraicCurve_RiemannRochRows
import tmp.external.ported.flt_th.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

/-!
# AG-FLT Riemann-Roch / Serre-duality rows + finite map data promotion
(first-class importable modules; audit component)

COMPONENT, not a paper object.  Named consumers: stepxi AG06b, stage4, Lead
AG-INFRA-PLAN, [Mzk1] GeometricCore build (RR + Serre duality + finite map layer).

Promotes the ported FLT modules (compiled green in
tmp/external/ported/flt/Definitions/Def_AlgebraicCurve_RiemannRochRows.lean and
tmp/external/ported/flt_th/Definitions/Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData.lean;
both Apache-2.0, attribution retained in the ported headers):
* RR statement rows: RiemannInequality, RiemannIndexFormula, WeilDualityAdelic,
  WeilDuality, WeilOmegaEllAgrees, FunctionFieldRiemannRoch;
* the two complete reduction theorems
  functionFieldRiemannRoch_of_riemann_and_duality and
  weilDuality_of_riemannIndex_of_adelic (proofs ported, no sorry);
* SmoothProperCurve.FiniteMapData (finite map to P1 data for GeometricCore).
No axiom/fake data.  The rows are statement definitions (Props) exactly as in
the source; the reductions are complete proofs.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.AG_FLT_RiemannRochPromotionActual

open LeanFormal.IUT

universe u

/-- RR row: Riemann inequality (statement row). -/
abbrev promotion_RiemannInequality (K F : Type) [Field K] [Field F] [Algebra K F] : Prop :=
  AlgebraicCurve.RiemannInequality K F

/-- RR row: Riemann index formula (statement row). -/
abbrev promotion_RiemannIndexFormula (K F : Type) [Field K] [Field F] [Algebra K F] : Prop :=
  AlgebraicCurve.RiemannIndexFormula K F

/-- RR row: adelic Weil duality (statement row; the Serre duality form). -/
abbrev promotion_WeilDualityAdelic (K F : Type) [Field K] [Field F] [Algebra K F] : Prop :=
  AlgebraicCurve.WeilDualityAdelic K F

/-- RR row: Weil duality (statement row). -/
abbrev promotion_WeilDuality (K F : Type) [Field K] [Field F] [Algebra K F] : Prop :=
  AlgebraicCurve.WeilDuality K F

/-- RR row: omega-space/ell agreement (statement row). -/
abbrev promotion_WeilOmegaEllAgrees (K F : Type) [Field K] [Field F] [Algebra K F] : Prop :=
  AlgebraicCurve.WeilOmegaEllAgrees K F

/-- RR row: function-field Riemann-Roch (statement row). -/
abbrev promotion_FunctionFieldRiemannRoch (K F : Type) [Field K] [Field F] [Algebra K F] : Prop :=
  AlgebraicCurve.FunctionFieldRiemannRoch K F

/-- COMPLETE proof (ported): Weil duality gives function-field Riemann-Roch. -/
theorem promotion_functionFieldRiemannRoch_of_riemann_and_duality
    (K F : Type) [Field K] [Field F] [Algebra K F]
    (hWD : AlgebraicCurve.WeilDuality K F) :
    AlgebraicCurve.FunctionFieldRiemannRoch K F :=
  AlgebraicCurve.functionFieldRiemannRoch_of_riemann_and_duality K F hWD

/-- COMPLETE proof (ported): Riemann index + adelic duality give Weil duality. -/
theorem promotion_weilDuality_of_riemannIndex_of_adelic
    (K F : Type) [Field K] [Field F] [Algebra K F]
    (hRI : AlgebraicCurve.RiemannIndexFormula K F)
    (hWD : AlgebraicCurve.WeilDualityAdelic K F) :
    AlgebraicCurve.WeilDuality K F :=
  AlgebraicCurve.weilDuality_of_riemannIndex_of_adelic K F hRI hWD

end LeanFormal.IUT.XiFPaper.AG_FLT_RiemannRochPromotionActual
