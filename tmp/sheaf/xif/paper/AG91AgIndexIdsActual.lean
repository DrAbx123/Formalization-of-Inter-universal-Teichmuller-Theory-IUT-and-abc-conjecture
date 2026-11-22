import LeanFormal.IUT.Audit.Status

/-! # AG91: INDEX.AG.* ids for the AG infrastructure chain

Ids for AG00 (Mathlib capability matrix) -> AG01 (curve foundations) ->
AG02 (function field / order of vanishing) -> AG03 (divisors / sections) ->
line bundles -> cohomology -> Riemann-Roch -> Serre duality -> basepoint-free
pencil -> Mzk1 GeometricCore.  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.AG91AgIndexIdsActual

/-- INDEX.AG.* ids with status/owner (data). -/
def AGIndexIds : List (String × String) :=
  [ ("INDEX.AG.ag00-mathlib-capability-matrix", "AG90MathlibAuditActual (lattice ledger); owner AG stream for AG00MathlibAuditActual"),
    ("INDEX.AG.ag01-curve-foundations", "AG01CurveFoundations (owner AG stream); reuse Mathlib Scheme/Over/Properties/Fiber/Limits/Normalization/ValuativeCriterion"),
    ("INDEX.AG.ag02-function-field", "AG02FunctionFieldActual (EXIT0 + CITABLE; Mathlib FunctionField/OrderOfVanishing reused; actual id INDEX.AG.function-field)"),
    ("INDEX.AG.ag02b-principal-divisor", "AG02bPrincipalDivisorActual (first new divisor layer; Mathlib divisor layer absent per AG00MathlibAuditActual:44-49)"),
    ("INDEX.AG.ag03-divisors-sections-realized", "AG03DivisorsSectionsActual (sections of O(D)) + AG03bSectionsBasicActual (basic sections); ids INDEX.AG.sections-OD / sections-basic"),
    ("INDEX.AG.ag05-ids-batch", "AG05IdsActual.agIds (SHA 6580AF1B); AG00bStep0RecordActual"),
    ("INDEX.AG.ag02-order-of-vanishing", "AG02OrderOfVanishing (owner AG stream); reuse OrderOfVanishing.lean:35 ordHom, :52 ord"),
    ("INDEX.AG.ag03-divisors-sections", "AG03DivisorsSections (owner AG stream); TO BUILD general divisors/sections"),
    ("INDEX.AG.ag04-line-bundles", "AG04LineBundles; PARTIAL-REUSE: Mathlib Modules/Sheaf/Tilde + FLT Def_AlgebraicCurve_DivisorClassGroup/CechSectionsOfDivisor (Apache-2.0, adapt) + PR #43392 open"),
    ("INDEX.AG.ag05-cohomology", "AG05Cohomology; PARTIAL-REUSE: Mathlib/CategoryTheory/Sites/SheafCohomology/{Basic,Cech,MayerVietoris}.lean (abstract sheaf cohomology) + FLT Cech sections; PR #36218 merged; coherent H^0/H^1 on curves still to build"),
    ("INDEX.AG.ag06-riemann-roch", "AG06RiemannRoch; ADAPT FLT Def_AlgebraicCurve_RiemannRochRows (Apache-2.0); PR #41621 open draft (conditional RR); chip-firing RR graphs arXiv 2606.16679 reference"),
    ("INDEX.AG.ag07-serre-duality", "AG07SerreDuality; ADAPT FLT Def_AlgebraicCurve_SerrePairing (Apache-2.0)"),
    ("INDEX.AG.ag08-basepoint-free-pencil", "AG08BasepointFreePencil; TO BUILD construction from adapted AG04 sections + AG06 RR; no Belyi formalization exists (Zulip Belyi/Dessins)"),
    ("INDEX.AG.ag09-mzk1-geometric-core", "AG09Mzk1GeometricCore; TO BUILD paper-input (corpus Noncritical Belyi Maps; depends on AG01-AG08)"),
    ("INDEX.AG.ag10-credits", "AG91/AG92/AG93 lattices: ids, dependency graph, Mathlib citation rows"),
    ("INDEX.AG.flt-adaptation.divisor-class-group", "AG_FLT_Def_AlgebraicCurve_DivisorClassGroup.lean (EXIT0; CITABLE 72 decls; Pic/Pic0/ord adapted)"),
    ("INDEX.AG.flt-adaptation.repartitions", "AG_FLT_Def_AlgebraicCurve_Repartitions.lean (EXIT0)"),
    ("INDEX.AG.flt-adaptation.adelic-index", "AG_FLT_Def_AlgebraicCurve_AdelicIndex.lean (EXIT0; CITABLE 68 decls; LSpace/ell/adeleSpace/globalSub)"),
    ("INDEX.AG.flt-adaptation.coherent-base-change", "AG_FLT_Def_AlgebraicGeometry_CoherentBaseChange.lean (EXIT0)"),
    ("INDEX.AG.flt-adaptation.pending", "AG_FLT_TwoChartCech + CechSectionsOfDivisor (pending compile; deps present), then SerrePairing/RiemannRochRows/SmoothProperCurveBase/FiniteMapData"),
    ("INDEX.AG.flt-adaptation.audit", "AG00bFLTAssetAuditActual.lean (EXIT0; no-axiom probe; flat naming/import rewrite rules)"),
    ("INDEX.AG.tauceti.weil-divisor", "TauCeti AlgebraicGeometry/WeilDivisor/** + Scheme/{LineBundle,Picard,PicZero,TensorProduct} (Apache-2.0; adapt) -> AG03/AG04"),
    ("INDEX.AG.tauceti.riemann-roch", "TauCeti WeilDivisor/Scheme/RiemannRoch/** + FieldTheory/FunctionField/RiemannRoch/** (incl Pencil) -> AG06/AG08"),
    ("INDEX.AG.tauceti.serre-duality", "TauCeti AlgebraicGeometry/LineBundle/SerreDuality + WeilDivisor/Scheme/SerdeDuality -> AG07"),
    ("INDEX.AG.tauceti.cohomology", "TauCeti WeilDivisor/Scheme/PrincipalParts/{Cohomology,FirstCohomology} + ResidueSequence/EulerCharacteristic -> AG05"),
    ("INDEX.AG.tauceti.belyi", "TauCeti FieldTheory/FunctionField/Belyi/** + Algebra/Polynomial/Belyi + RiemannSurface/BelyiPair -> NCBel/AG09 infra (GeometricCore D remains)"),
    ("INDEX.AG.external-flt-repo", "EXTERNAL ASSET tmp/external/flt-lean (local clone of github.com/anthropics/fermats-last-theorem; Apache-2.0; 1450 lean files): Definitions/Def_AlgebraicCurve_{DivisorClassGroup,AdelicIndex,CechSectionsOfDivisor,SerrePairing,RiemannRochRows}.lean + Def_AlgebraicGeometry_{SmoothProperCurveBase,SmoothProperCurveFiniteMapData}.lean"),
    ("INDEX.AG.mathlib-sheaf-cohomology", "Mathlib/CategoryTheory/Sites/SheafCohomology/{Basic,Cech,MayerVietoris}.lean: H/cohomologyPresheafFunctor/H.equiv0/Cech/MV (abstract sheaf cohomology; PARTIAL-REUSE)"),
    ("INDEX.AG.upstream-prs", "Mathlib PR #36218 merged (sheaf cohomology exact sequences); #43392 open (sheaves of modules cohomology API); #41621 open draft (conditional RR)"),
    ("INDEX.AG.roadmap-context", "Mochizuki-Hoshi-Yamashita-Yang Formalization of IUT (2026-04): papers/motizuki_corpus/text/Formalization of IUT (2026-04).txt roadmap Stage 1-5 + four triangles; LANA report papers/LANA_report_202607.pdf + text tmp/external/lana_report_202607.txt; Stoll heights talk; Cambridge Brauer/group cohomology in Lean4 seminar; arXiv 2606.16679 chip-firing RR graphs") ]

theorem AGIndexIds_length : AGIndexIds.length = 30 := rfl

end LeanFormal.IUT.XiFPaper.AG91AgIndexIdsActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: AG ids. -/
def AGIndexIdsRecord : Obligation :=
  { id := "INDEX.AG.ids"
    source := "Lead AG order; Mathlib AlgebraicGeometry audit (AG90); coord/PRIOR-ART-INDEX.md"
    status := VerificationStatus.interface
    note := "INDEX.AG ids (30, incl. stepxi AG layer + FLT adaptation + TauCeti assets): AG00 Mathlib capability matrix (AG90 ledger), AG01 curve foundations (Mathlib reuse), AG02 function field + order of vanishing (Mathlib reuse), AG03 divisors/sections (to build), AG04 line bundles (PARTIAL-REUSE: Mathlib modules + FLT divisor class group/Cech sections, PR #43392), AG05 cohomology (PARTIAL-REUSE: Mathlib SheafCohomology Basic/Cech/MV, not only ell-adic; PR #36218; coherent H0/H1 still to build), AG06 RR (ADAPT FLT RiemannRochRows; PR #41621 draft; chip-firing RR graphs arXiv 2606.16679), AG07 Serre duality (ADAPT FLT SerrePairing), AG08 basepoint-free pencil (to build), AG09 Mzk1 GeometricCore (paper-input; no Belyi formalization), plus TauCeti adapt ids (weil-divisor/riemann-roch/serre-duality/cohomology/belyi; Apache-2.0 primary source for AG03-AG08/NCBel infra) and external-flt-repo / mathlib-sheaf-cohomology / upstream-prs / roadmap-context ids and FLT adaptation batch ids (divisor-class-group/Repartitions/AdelicIndex/CoherentBaseChange green; TwoChartCech/CechSectionsOfDivisor pending; RR/Serre/curve base/finite-map data next; audit AG00bFLTAssetAuditActual). Registry frozen 14041."
    dependsOn := ["AG91AgIndexIdsActual", "INDEX.AG.mathlib-capability-matrix"] }

end LeanFormal.IUT.Audit