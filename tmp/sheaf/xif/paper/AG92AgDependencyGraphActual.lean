import LeanFormal.IUT.Audit.Status

/-! # AG92: AG infrastructure DEPENDENCY GRAPH

Chain: Mathlib capability -> curve -> function field/order of vanishing ->
divisors/sections -> line bundles/sections -> cohomology -> Riemann-Roch ->
Serre duality -> basepoint-free pencil -> Mzk1 GeometricCore.
Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.AG92AgDependencyGraphActual

/-- AG dependency rows: (node, depends on, required content, status). -/
def AGDependencyGraph : List (String × String × String × String) :=
  [ ("AG01.curve-foundations", "Mathlib Scheme/Over/Properties/Fiber/Limits/Normalization/ValuativeCriterion", "curve = integral separated finite-type scheme over a field; geometric curve; proper/smooth", "Mathlib AVAILABLE; adapt"),
    ("AG02.function-field", "AG01 + Mathlib FunctionField.lean:37/41/148; REALIZED in AG02FunctionFieldActual (EXIT0 + CITABLE)", "function field of an integral curve; fractions", "REALIZED (Mathlib reuse)"),
    ("AG02b.principal-divisor", "AG02FunctionFieldActual + OrderOfVanishing; REALIZED in AG02bPrincipalDivisorActual (first new divisor layer)", "principal divisors / order of vanishing global", "REALIZED first layer (Mathlib divisor layer absent)"),
    ("AG03.sections-OD", "AG02bPrincipalDivisorActual + AG03DivisorsSectionsActual + AG03bSectionsBasicActual", "sections of O(D), basic sections", "REALIZED first layer"),
    ("AG02.order-of-vanishing", "AG01 + Mathlib OrderOfVanishing.lean:35 ordHom/:52 ord", "order of vanishing at closed points (coheight-1)", "Mathlib AVAILABLE (coheight-1); reuse"),
    ("AG03.divisors", "AG02.order-of-vanishing + TAUCETI AlgebraicGeometry/WeilDivisor/** + FieldTheory/FunctionField/Divisor/** (Apache-2.0, adapt) + FLT adapted AG_FLT_Def_AlgebraicCurve_DivisorClassGroup (CITABLE 72 decls) + Repartitions + AdelicIndex", "Weil divisors, degree, principal divisors, linear equivalence, repartitions/adelic index", "REUSE/ADAPT (TauCeti primary + FLT adapted)"),
    ("AG03.sections", "AG03.divisors + AG_FLT_Def_AlgebraicCurve_CechSectionsOfDivisor (pending compile; deps Repartitions+CoherentBaseChange+TwoChartCech present) + Mathlib Modules/Sheaf/Tilde", "sections of O(D) / global sections H^0", "PENDING ADAPT (deps ready)"),
    ("AG04.line-bundles", "AG03.divisors + AG_FLT_DivisorClassGroup (Pic/Pic0/IsPrincipal adapted) + AG_FLT_AdelicIndex + Mathlib Modules/Sheaf/Tilde; PR #43392 open", "invertible sheaves, tensor product, Pic group, very ample", "PARTIAL-REUSE (Pic/Pic0 realized; Cech sections pending)"),
    ("AG05.cohomology-abstract", "Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean (H, cohomologyPresheafFunctor, H.equiv0) + Cech.lean + MayerVietoris.lean; Mathlib PR #36218 merged (sheaf cohomology exact sequences)", "abstract abelian-sheaf cohomology, Cech, exact sequences, MV", "PARTIAL-REUSE (Mathlib; not only ell-adic)"),
    ("AG05.cohomology", "AG03/AG04 + AG05.cohomology-abstract + FLT tmp/external/flt-lean Def_AlgebraicCurve_CechSectionsOfDivisor (Apache-2.0, local clone) + PR #43392 open (sheaves of modules cohomology API)", "coherent H^0/H^1 on curves (Serre finiteness)", "PARTIAL-REUSE/ADAPT: abstract+FLT pieces reused; curve-level H0/H1 still to build"),
    ("AG06.riemann-roch", "AG03 + AG04 + AG05 + FLT tmp/external/flt-lean Def_AlgebraicCurve_RiemannRochRows (Apache-2.0, local clone) + Mathlib PR #41621 open draft (conditional RR chi(O_X(D)) = deg + chi(O_X))", "Riemann-Roch for divisors on a curve", "ADAPT: FLT RR rows + PR #41621; chip-firing RR graphs arXiv 2606.16679 as combinatorial reference"),
    ("AG07.serre-duality", "AG05 + AG06 + FLT tmp/external/flt-lean Def_AlgebraicCurve_SerrePairing (Apache-2.0, local clone)", "Serre duality H^1(K-D) dual to H^0(D)", "ADAPT: FLT Serre pairing; no Mathlib asset"),
    ("AG08.basepoint-free-pencil", "AG04 + AG06 (RR + sections) + FLT tmp/external/flt-lean Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData (Apache-2.0, local clone; adapt)", "basepoint-free pencil from two independent sections of O(D)", "TO BUILD construction; FLT finite-map data adapted"),
    ("AG09.mzk1-geometric-core", "AG01-AG08 + corpus Noncritical Belyi Maps + TAUCETI FieldTheory/FunctionField/Belyi/** + Algebra/Polynomial/Belyi + RiemannSurface/BelyiPair (Belyi infra, adapt)", "noncritical Belyi map existence / geometric core (paper-input)", "ADAPT Belyi infra (TauCeti) + D paper-input for noncritical GeometricCore; feeds GenEll05 reverse direction/P2"),
    ("GenEll05.ii-implies-i", "AG09 + Prop 1.4/1.6/1.7", "GenEll05Theorem21Actual.Theorem21ReductionInputs (noncriticalBelyiExists, coverConstruction, bdClassChain, compactlyBoundedData)", "consumer: P2/P0 chain; no fake closure"),
    ("IUT-IV-section2-consumer", "GenEll05/AG09 + IUT IV Thm 1.10", "GenEll08MainReductionActual.GenEllIUTIVSection2Consumer replaces Section2.lean machine-gap", "P3 integration target (stepxi)"),
    ("AG.roadmap-context", "Mochizuki-Hoshi-Yamashita-Yang Formalization of IUT (2026-04) roadmap Stage 1-5 + four-triangle decomposition (BPS/etHT/dsc/HDD/SHE/IPL/APT/Ind1,2,3, Thm 3.11/3.11.5/Cor 3.12); LANA report (papers/LANA_report_202607.pdf; text tmp/external/lana_report_202607.txt; github.com/katobungen/LANA_report_202607), MHYY report (papers/motizuki_corpus/text/Formalization of IUT (2026-04).txt); Stoll Formalizing Heights talk; Cambridge Brauer/group cohomology in Lean4 seminar", "program alignment/context for AG chain", "CONTEXT (no proof content)") ]

end LeanFormal.IUT.XiFPaper.AG92AgDependencyGraphActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: AG dependency graph. -/
def AGDependencyGraphRecord : Obligation :=
  { id := "INDEX.AG.dependency-graph"
    source := "AG90 capability matrix; AG91 ids; Mathlib AlgebraicGeometry audit; GenEll plan"
    status := VerificationStatus.interface
    note := "AG DEPENDENCY GRAPH (18 rows; AG03-AG08 now REUSE/ADAPT TauCeti primary + FLT secondary; AG05 partial; AG09 Belyi infra from TauCeti, GeometricCore D): Mathlib capabilities (Scheme/Over/Properties/Fiber/Limits/Normalization/ValuativeCriterion, FunctionField, OrderOfVanishing, RationalMap, Modules/Sheaf/Tilde, CategoryTheory/Sites/SheafCohomology Basic/Cech/MayerVietoris) -> AG01 curve -> AG02 function field/ord -> AG03 divisors/sections (FLT divisor class group/adelic index adapt) -> AG04 line bundles (FLT Cech sections; PR #43392) -> AG05 cohomology (Mathlib abstract cohomology + FLT Cech; PR #36218 merged; curve-level H0/H1 to build) -> AG06 RR (FLT RR rows; PR #41621 draft; chip-firing RR graphs arXiv 2606.16679) -> AG07 Serre duality (FLT Serre pairing) -> AG08 basepoint-free pencil (build; FLT finite map data adapt) -> AG09 Mzk1 GeometricCore (paper-input; no Belyi formalization per Zulip) -> GenEll05 reverse direction + IUT IV section2 consumer. FLT repo = anthropics/fermats-last-theorem (Apache-2.0, external source-only); roadmap context = Mochizuki-Hoshi-Yamashita-Yang Formalization of IUT (2026-04) + LANA report + Stoll heights talk + Cambridge Brauer seminar. No re-proof; no axioms; registry frozen 14041."
    dependsOn := ["AG92AgDependencyGraphActual", "INDEX.AG.ids", "INDEX.GENELL.dependency-map"] }

end LeanFormal.IUT.Audit
