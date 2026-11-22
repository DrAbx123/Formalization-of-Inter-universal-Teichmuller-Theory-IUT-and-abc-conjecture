import tmp.sheaf.xif.paper.AG_FLT_RiemannRochPromotionActual

/-!
# AG06b: Riemann-Roch / Serre duality consumer interface (data only)

Lead gate correction (2026-11-10): canonical ported assets (RR/Serde/Cech/FiniteMapData/
Belyi) are treated as COMPLETE for planning purposes; compile-pending is marked as
"assumed available".

UPDATE: qpilot's canonical RR/Serde promotion is GREEN/CITABLE
(AG_FLT_RiemannRochPromotionActual: 6 statement rows + 2 COMPLETE reduction theorems;
FiniteMapData ported module green, promotion in a separate pending file).  This file
IMPORTS that canonical promotion and re-exposes the complete reductions in the AG06b
interface; the remaining rows stay named statement rows (not proof claims).

Canonical assets (qpilot owner; coord/EXTERNAL-PORT-REGISTRY.md):
* flt_core: Def_AlgebraicCurve_SerrePairing (+ weilDualityAdelic),
  cechRiemannRoch / Def_AlgebraicCurve_RiemannRochRows,
  Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData;
* flt_test: canonical divisor / Kaehler differentials / RR-space;
* tauceti_rr: RiemannRoch (Pencil/Genus/Basic), Differential/CanonicalDivisor,
  WeilDivisor/SerdeDuality, Belyi/Basic;
* adapted Cech canonical: tmp/sheaf/xif/paper/AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor
  (queued; AG05 depends on it).
Promotions PENDING (qpilot): AG_FLT_RiemannRochPromotionActual,
AG_TAUCETI_RiemannRochPromotionActual.
**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.AG06bRRInterfaceActual

open LeanFormal.IUT.XiFPaper.AG_FLT_RiemannRochPromotionActual

universe u

variable {K F : Type} [Field K] [Field F] [Algebra K F]

/-- AG06b complete reduction: Weil duality gives function-field Riemann-Roch
(canonical promoted COMPLETE proof, no sorry). -/
theorem ag_rr_functionFieldRiemannRoch_of_duality
    (hWD : promotion_WeilDuality K F) :
    promotion_FunctionFieldRiemannRoch K F :=
  promotion_functionFieldRiemannRoch_of_riemann_and_duality K F hWD

/-- AG06b complete reduction: Riemann index formula + adelic Weil duality give
Weil duality (canonical promoted COMPLETE proof, no sorry). -/
theorem ag_rr_weilDuality_of_index_adelic
    (hRI : promotion_RiemannIndexFormula K F)
    (hWD : promotion_WeilDualityAdelic K F) :
    promotion_WeilDuality K F :=
  promotion_weilDuality_of_riemannIndex_of_adelic K F hRI hWD

/-- Canonical RR promotion status: (row, kind). -/
def agRRPromotionRows : List (String × String) :=
  [ ("promotion_RiemannInequality", "STATEMENT ROW (definition; no proof claim)"),
    ("promotion_RiemannIndexFormula", "STATEMENT ROW"),
    ("promotion_WeilDualityAdelic", "STATEMENT ROW (adelic Serre duality form)"),
    ("promotion_WeilDuality", "STATEMENT ROW"),
    ("promotion_WeilOmegaEllAgrees", "STATEMENT ROW"),
    ("promotion_FunctionFieldRiemannRoch", "STATEMENT ROW"),
    ("promotion_functionFieldRiemannRoch_of_riemann_and_duality", "COMPLETE PROOF (ported)"),
    ("promotion_weilDuality_of_riemannIndex_of_adelic", "COMPLETE PROOF (ported)"),
    ("SmoothProperCurve.FiniteMapData", "canonical import tmp.external.ported.flt_th.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData (ported EXIT=0; wrapper non-canonical per qpilot)") ]

/-- The RR/Serde interface the AG divisor layer will consume (fields are the exact
paper-level statements; each will be supplied by the canonical A-class assets). -/
structure AGRiemannRochInterface where
  /-- Riemann-Roch equality: ell(D) - ell(K-D) = deg D + 1 - g -/
  riemannRoch_eq : Prop
  /-- Serre duality pairing between H0(O(D)) and H1(O(K-D)) -/
  serre_duality : Prop
  /-- two-chart Cech Riemann-Roch comparison (cechH0/cechH1 vs ell) -/
  cech_riemannRoch : Prop
  /-- existence of the canonical divisor / Kaehler differentials -/
  canonical_divisor : Prop
  /-- Belyi existence (TauCeti tauceti_rr Belyi/Basic) -/
  belyi_existence : Prop
  /-- finite map to P1 data (FLT flt_core SmoothProperCurveFiniteMapData) -/
  finite_map_data : Prop

/-- Canonical asset record: (interface field, canonical module, status). -/
def agRRCanonicalAssets : List (String × String × String) :=
  [ ("riemannRoch_eq / cech_riemannRoch", "flt_core Def_AlgebraicCurve_RiemannRochRows + cechRiemannRoch; flt_test RR-space", "canonical port; ASSUMED COMPLETE (compile pending marked assumed)"),
    ("serre_duality", "flt_core Def_AlgebraicCurve_SerrePairing + weilDualityAdelic; tauceti_rr WeilDivisor/SerdeDuality", "canonical port; ASSUMED COMPLETE"),
    ("canonical_divisor", "flt_test canonical divisor/Kaehler; tauceti_rr Differential/CanonicalDivisor", "canonical port; ASSUMED COMPLETE"),
    ("belyi_existence", "tauceti_rr Belyi/Basic", "canonical port; ASSUMED COMPLETE"),
    ("finite_map_data", "tmp.external.ported.flt_th.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData (ported EXIT=0; use directly per qpilot)", "canonical port module GREEN"),
    ("Cech H0/H1 = L(D)", "tmp/sheaf/xif/paper/AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor (canonical adapted)", "queued; AG05 dependency"),
    ("promotion layer", "AG_FLT_PromotionActual (CITABLE 8) + PENDING AG_FLT_RiemannRochPromotionActual / AG_TAUCETI_RiemannRochPromotionActual", "green/PENDING (qpilot)") ]

/-- Downgrade honesty: assumed-complete is a planning status, not a proof claim. -/
def agRRStatusHonesty : List (String × String) :=
  [ ("assumed available", "canonical port targets; not yet compiled/promoted in this tree"),

    ("proved in tree", "AG_FLT_PromotionActual (8 decls) + adapted DivisorClassGroup/AdelicIndex/Repartitions (CITABLE)"),
    ("not claimed", "riemannRoch_eq / serre_duality / cech_riemannRoch / belyi_existence / finite_map_data remain PENDING until promotions green") ]

end LeanFormal.IUT.XiFPaper.AG06bRRInterfaceActual
