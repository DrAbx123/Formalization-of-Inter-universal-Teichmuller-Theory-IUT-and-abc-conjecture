/-!
# S3171d: FLT-ported asset support for IV §1 / (b) — classification (data only)

External prior art: FLT Lean repo (https://github.com/anthropics/fermats-last-theorem,
Apache-2.0; local raw clone tmp/external/flt-lean, 1450+ lean files under
Definitions/).  Adaptation policy: copy + import rewrite, namespaces/declarations
preserved (see AG00bFLTAssetAuditActual).

ADAPTED AND PRESENT (tmp/sheaf/xif/paper/AG_FLT_*.lean):
* AG_FLT_Def_AlgebraicCurve_DivisorClassGroup — AG-01a place/divisor/degree/
  IsPrincipal/Pic (Mathlib-only imports).
* AG_FLT_Def_AlgebraicCurve_Repartitions — AG-02a adeles/repartitions.
* AG_FLT_Def_AlgebraicCurve_AdelicIndex — AG-02a LSpace/ell/adeleBdd/repartitions/
  adelic index (the LSpace/ell = H0 layer).
* AG_FLT_Def_AlgebraicGeometry_TwoChartCech — AG-03a two-chart Cech complex for P1.
* AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor — AG-03a lSpaceOn/cechDiff/
  cechH0/cechH1/H1 for divisor line bundles.
* AG_FLT_Def_AlgebraicGeometry_CoherentBaseChange — AG-03b coherent base change.
PENDING ADAPTATION (raw only; not yet copied):
* Def_AlgebraicCurve_RiemannRochRows (tmp/external/flt-lean/Definitions/...).
* Def_AlgebraicCurve_SerrePairing + Def_AlgebraicGeometry_TwoChartCechSerrePairingInt.
* Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData (+ SmoothProperCurveBase) —
  finite map to P1.
USE FOR IV §1 / (b):
* The FLT divisor/Cech/Serre layer is the future AG-03/AG-04 divisor layer (ℓ(D),
  Serre duality, H0/H1) — it does NOT directly support the Thm 1.10 display;
  its value for the paper route is the AG-side Riemann-Roch prerequisites
  (AG03/AG04 current first/second layers are Mathlib-based; see AG02-AG04 files).
* The (b) uniform height comparison IS supported by the pinned Mathlib height layer
  (Mathlib.NumberTheory.Height.NumberField) through production
  ABCHeightArithmeticWeightComparison (reused in S3171UniformHeightConsumerActual).
* Nothing here is importable from vendor; FLT adapted copies are importable once
  placed (AG_FLT_* files are standalone adapted modules).
Honest class: FLT assets = external prior art; adapted files carry attribution;
pending ones must NOT be counted until adapted+compiled.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.S3171FLTAssetSupportActual

/-- FLT asset status row: (module, status, use for IV §1 / (b)). -/
def s3171FLTAssets : List (String × String × String) :=
  [ ("AG_FLT_Def_AlgebraicCurve_DivisorClassGroup", "ADAPTED (present)", "AG divisor/degree/Pic layer (future AG-03)"),
    ("AG_FLT_Def_AlgebraicCurve_Repartitions", "ADAPTED (present)", "AG adeles/repartitions (future AG-02)"),
    ("AG_FLT_Def_AlgebraicCurve_AdelicIndex", "ADAPTED (present)", "LSpace/ell = H0 layer (future AG-03)"),
    ("AG_FLT_Def_AlgebraicGeometry_TwoChartCech", "ADAPTED (present)", "two-chart Cech complex for P1 (future AG-03)"),
    ("AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor", "ADAPTED (present)", "cechH0/cechH1/H1 of divisor line bundles (future AG-03)"),
    ("AG_FLT_Def_AlgebraicGeometry_CoherentBaseChange", "ADAPTED (present)", "coherent base change (future AG-03)"),
    ("Def_AlgebraicCurve_RiemannRochRows", "PENDING adaptation (raw only)", "Riemann-Roch rows (future AG-04; not counted)"),
    ("Def_AlgebraicCurve_SerrePairing", "PENDING adaptation (raw only)", "Serre pairing (future AG-04; not counted)"),
    ("Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData", "PENDING adaptation (raw only)", "finite map to P1 (future AG-02; not counted)"),
    ("Mathlib.NumberTheory.Height.NumberField", "PINNED Mathlib (reuse)", "(b) uniform height comparison via production ABCHeightArithmeticWeightComparison"),
    ("abcRationalPoint_logHeight₁_le_mul_arithmeticWeight_of_uniform_valuation_bound", "REUSED production theorem", "(b) H1 conditional reduction (S3171UniformHeightConsumerActual)") ]

end LeanFormal.IUT.XiFPaper.S3171FLTAssetSupportActual
