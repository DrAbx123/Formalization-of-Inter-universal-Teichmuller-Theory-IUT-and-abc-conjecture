import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# AG-00b: FLT asset audit (external prior art, Apache-2.0) — audit component

COMPONENT, not a paper object.  Named consumers: coord/AG-INFRA-PLAN.md,
AG_adapt/* adapted modules.

The FLT Lean repository (https://github.com/anthropics/fermats-last-theorem,
Apache-2.0) is a local prior-art asset at tmp/external/flt-lean.  This file
records the module -> our AG layer mapping and the required adaptation for our
lake layout (import rewrite only; namespaces/declarations preserved).  The
adapted copies live in tmp/sheaf/xif/paper/AG_adapt/ with attribution headers.
No axiom, no fake data: the audit is literal data plus kernel-checked rfl facts.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.AG00bFLTAssetAuditActual

/-- An adapted FLT module. -/
structure FLTAsset where
  module : String
  file : String
  agLayer : String
  adaptation : String

/-- FLT modules adapted for the AG build (import rewrite to our lake layout). -/
def FLTAssets : List FLTAsset :=
  [ { module := "Def_AlgebraicCurve_DivisorClassGroup",
      file := "Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean",
      agLayer := "AG-01a place/divisor/degree/IsPrincipal/Pic (Mathlib-only imports)",
      adaptation := "copy; import rewrite to tmp.sheaf.xif.paper.AG_adapt" },
    { module := "Def_AlgebraicCurve_Repartitions",
      file := "Definitions/Def_AlgebraicCurve_Repartitions.lean",
      agLayer := "AG-02a adeles/repartitions (depends on DivisorClassGroup)",
      adaptation := "copy; import rewrite" },
    { module := "Def_AlgebraicCurve_AdelicIndex",
      file := "Definitions/Def_AlgebraicCurve_AdelicIndex.lean",
      agLayer := "AG-02a LSpace/ell/adeleBdd/repartitions/adelic index",
      adaptation := "copy; import rewrite (imports Mathlib + Repartitions)" },
    { module := "Def_AlgebraicGeometry_TwoChartCech",
      file := "Definitions/Def_AlgebraicGeometry_TwoChartCech.lean",
      agLayer := "AG-03a two-chart Cech complex for P1",
      adaptation := "copy; import rewrite" },
    { module := "Def_AlgebraicCurve_CechSectionsOfDivisor",
      file := "Definitions/Def_AlgebraicCurve_CechSectionsOfDivisor.lean",
      agLayer := "AG-03a lSpaceOn/cechDiff/cechH0/cechH1/H1 for divisor line bundles",
      adaptation := "copy; import rewrite" } ]

/-- Five FLT modules are adapted in this batch. -/
theorem FLTAssets_length : FLTAssets.length = 5 :=
  rfl

/-- The divisor module is adapted first (Mathlib-only imports). -/
theorem FLTAssets_divisor_mem :
    (FLTAssets.map (fun a => a.module)).contains
      "Def_AlgebraicCurve_DivisorClassGroup" = true :=
  rfl

end LeanFormal.IUT.XiFPaper.AG00bFLTAssetAuditActual
