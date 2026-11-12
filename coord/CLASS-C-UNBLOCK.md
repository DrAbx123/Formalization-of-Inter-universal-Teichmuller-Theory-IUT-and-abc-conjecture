# CLASS-C-UNBLOCK — six C-route component unblock tracking

Live snapshot (2026-11-12). Source-vs-compiled counts are from the actual tree/olean dirs; `%` is compiled/source.

## 0. Port progress numbers

| source | files | compiled | % | note |
|---|---|---|---|---|
| FLT271 (`tmp/external/flt271`) | 271 | 0 | 0% | 260 FLT + 2 FLTTest + 6 blueprint-verso; Patching 14 = 7 顶层 + 7 Utils, import 闭包 19; toolchain v4.35.0 |
| anthro Definitions (`tmp/external/flt-defs`) | 1450 | 0 | 0% | toolchain v4.33.1; Def_ModularCurve 291, Def_AutomorphicForm 106, Def_CuspForm 32, Def_Hecke 10, Def_ModularForm 5 |
| flt-regular (`tmp/vendor_clone_flt_regular`) | 25 | 0 | 0% | toolchain v4.36.0-rc2; regular-prime case only |
| Mathlib ModularForms | 19 | 38 oleans | 100% | project Mathlib green; includes Petersson integrand, q-expansions, discriminant |
| FLT port (`tmp/external/ported/flt`) | 131 | 14 | 10.7% | Frey/Galois/deformation skeleton |
| vendor Heights | 64 | 56 | 87.5% | `SilvermanHeight` NOT compiled; no Arakelov/Faltings equality |
| vendor EllipticCurves | 480 | 25 | 5.2% | torsion only green; Basic/NeronOggShafarevich not compiled |
| vendor CurvesJacobian | 590 | 0 | 0% | no green oleans |
| vendor WeilCurves | 49 | 0 | 0% | no green oleans |
| vendor Oka | 828 | 123 | 14.9% | low C-route value; 9 axiom files upstream |
| vendor FormalSchemes | 647 | 77 | 11.9% | 2 axiom files upstream |

## 1. Six component matrix

| component | target definition | source port | current status | next step | risk |
|---|---|---|---|---|---|
| **newform** | `Newform` subspace of `CuspForm k Γ0(N)`, Hecke eigenform, q-expansion, Atkin–Lehner | **anthro** `Def_CuspForm_Newforms`, `Def_CuspForm_NewLattice`, `Def_ModularForm_AtkinLehnerDatum`, `Def_CuspForm_AtkinLehnerOperator`; Mathlib `CuspForm` base | language present (anthro 0 compiled); Mathlib base green; **no newform theorem green** | port anthro `Def_CuspForm` 32 + `Def_Hecke` 10 + `Def_ModularForm` 5 (toolchain v4.33.1→v4.32.2), then define newform/eigensystem | high: version drift, 0 anthro compiled, no newform proof |
| **Shimura** | Shimura curve `X^D(N)` (quaternionic), canonical model, Hecke correspondences | **anthro** 8 Shimura files: `Def_CerednikDrinfeld_ShimuraCurve`, `Def_ModularCurve_Shimura{Subgroup,Covering,Generator,Kernel}`, `Def_HeckeGalois_EichlerShimura`, `Def_FreyPackage_MazurEichlerShimuraFamily`; no Mathlib/vendor | definitions present (0 compiled); **no Shimura construction/theorem green** | port 8 anthro Shimura files; build quaternion algebra + Shimura curve model | very high: geometry missing, 0 compiled |
| **δ (parameterization degree)** | `deg(X_0(N) -> E)`, modular parameterization degree bound δ | **NONE**: no `Def_Parametrization`/`Delta`/degree asset; closest `Def_TateCurve_TorsionParametrization` is a different object; FLT271 none | **absent** | self-build modular curve morphism/degree API on top of anthro `Def_ModularCurve` language | very high: no source anywhere; needs new geometry |
| **Faltings height** | Arakelov/Faltings height h_F(E), period integration, Hodge metric comparison | **vendor Heights** `ArchimedeanAlgebraicRealization` green, `Curve/{CondHeight,DivisorHeight,TupleHeight,Conductor}` green; `SilvermanHeight` NOT compiled and explicitly says it does NOT prove Arakelov/Faltings; anthro Faltings=0 | scaffold green; **Faltings height ABSENT** | compile `SilvermanHeight`, connect formula height to Arakelov period integration; add Faltings height definition | high: analytic metric/period integration missing |
| **Néron period** | Néron model, special fibre, component group, period pairing | **anthro** 26 Néron files (`Def_AlgebraicGeometry_Neron*`, `Def_ModularCurve_J*Neron*`, `Def_NeronModelInfra_*`); green `Definitions/...NeronModelPropertyBundleCarrier`; vendor `EllipticCurves/Reduction/NeronOggShafarevich` not compiled | carriers/definitions only; **0 anthro compiled**, no period pairing | port 26 anthro Néron definitions; compile vendor EllipticCurves reduction/Néron–Ogg–Shafarevich | medium-high: definitions exist, no compiled period theory |
| **Petersson norm** | Petersson inner product/norm on cusp forms; norm estimates | **Mathlib** `ModularForms/Petersson.lean` green (`petersson` integrand only); **anthro** `Def_CuspForm_Petersson`, `PeterssonOn`, `PeterssonCoset`, `Def_AutomorphicForm_PeterssonIntegral` | integrand green (Mathlib); **no norm/estimate green**; anthro 0 compiled | port anthro 4 Petersson defs; prove positivity/norm estimates on cusp forms | medium: Mathlib base is green; estimates missing |

## 2. Best source per component

- **newform** → anthro (CuspForm/Hecke/ModularForm language) + Mathlib base.
- **Shimura** → anthro (8 Shimura files); nothing in Mathlib/vendor.
- **δ** → no source; self-build.
- **Faltings height** → vendor Heights scaffold + self-build; anthro has 0 Faltings files.
- **Néron period** → anthro 26 Néron definitions; vendor EllipticCurves reduction as secondary.
- **Petersson norm** → Mathlib integrand + anthro cusp-form Petersson definitions.

## 3. Upstream sorry/axiom (NOT evidence)

| source | sorry files | axiom files | action |
|---|---|---|---|
| FLT271 | **70** | **3 axiom declarations** | do NOT use as evidence until sorry/axiom removed; 3 axiom declarations in `FLT/Assumptions/{KnownIn1980s,Mazur,Odlyzko}.lean` (stage4 audit A868) |
| FLT port (`tmp/external/ported/flt`) | 5 | 1 | skeleton only; `KnownIn1980s`, `Torsion`, `Automorphic`, `Frey`, `GaloisRep` |
| EllipticCurves | 9 | 1 | `FormalGroup/*`, `TateModule/MatrixRepBasisChangeThree`, `Reduction/KernelFormalGroup`, `Torsion/WardR1*`, `FunctionField/PullbackPrincipalityNGeneral`; `FormalGroup/LogAdditivity` axiom |
| Oka | 0 | 9 | `AnalyticSpace/*` + `Topology/Maps/Proper/Basic` axioms; low C value |
| FormalSchemes | 0 | 2 | `FormalGm`, `GlueDataSectionGlue` axioms |
| anthro / flt-regular / Heights / CurvesJacobian / WeilCurves | 0 | 0 | no upstream sorry/axiom detected |
| Mathlib ModularForms | 0 actual (only a comment mentions sorry) | 0 | green |

## 4. Unblock order (C-route value)

1. **Mathlib ModularForms** (zero cost, green): use `CuspForm`, `qExpansion`, `discriminant`, `petersson` as the base.
2. **anthro language subset** (lowest cost): `Def_CuspForm` 32 + `Def_Hecke` 10 + `Def_ModularForm` 5 → newform/Petersson language; then `Def_ModularCurve` 291 subset for Shimura/δ.
3. **vendor Heights** remaining 8, especially compile `SilvermanHeight` and connect to `ArchimedeanAlgebraicRealization` → Faltings scaffold.
4. **anthro Néron 26** definitions → Néron period language.
5. **δ**: self-build; no port source exists.
6. **FLT271**: port source only after toolchain adaptation; actual local count = **271 lean / 70 sorry / 3 axiom declarations**; not evidence.

## 5. Blockers summary

- Toolchain drift: project v4.32.2 vs FLT271 v4.35.0, anthro v4.33.1, flt-regular v4.36.0-rc2 — expect first error `unknown module` / `unknown identifier` / typeclass mismatch, not mathematical errors.
- anthro 1450 and FLT271 271 have **0 compiled oleans**; first port step is compile/adaptation, not proof.
- Six-component state: newform/Petersson = language only; Shimura/Néron = definitions only; δ/Faltings = absent.


## 6. Stage4 anthro mapping and port priority (A854)

Source of truth: `coord/PORT-SOURCES-AUDIT.md` §6 (anthro `Theorems/` entries, whose real work is in the `P2M/Sol` closure). Counts are file-name matches, not reviewed content; toolchain v4.33.1 -> project v4.32.2 still applies.

### 6.1 Six C-route components -> anthro target

| C component | anthro target / file evidence | match count | status |
|---|---|---|---|
| **newform** | `Thm_CuspForm_exists_isNewform_descent`, `Thm_CuspForm_atkinLehnerLin_*isNewform*`; `Def_CuspForm_Newforms` | 101 + 436 + 179 (Newform/CuspForm/Hecke) | language/definition present; no green proof in project |
| **Shimura** | `Thm_CerednikDrinfeld_ShimuraCurveModel_*` (goodReduction/eichlerShimura); `Def_CerednikDrinfeld_ShimuraCurve` | 28 Shimura + 750 EllipticCurve_ QM/fake EC | definitions present; **deferred with ModularCurve 7708** |
| **δ (parameterization degree)** | **no dedicated anthro target in the stage4 list**; closest `ModularCurve` (7,708) and Tate parametrization definition only | 0 direct | absent; self-build / deferred ModularCurve |
| **Faltings height** | Heights class in anthro: names containing `Height` (Mathlib-level lemmas); vendor `Heights` scaffold | 199 | scaffold only; no Faltings height equality |
| **Néron period** | no dedicated stage4 theorem; anthro 26 `Def_Neron*`/`J*Neron*` definitions | 26 definitions | definitions only; no period pairing |
| **Petersson norm** | no dedicated stage4 theorem; Mathlib `petersson` integrand + anthro 4 `Def_CuspForm_Petersson*` | 4 definitions + Mathlib | integrand only; no norm estimates |

Stage4 arithmetic-side targets (support the C route but are not the six analytic components):

| stage4 target | anthro entry | match count | C use |
|---|---|---|---|
| Frey modularity | `Thm_FreyPackage_frey_isModular` | 64 Frey-package matches | C1 core |
| level lowering | `Thm_FreyPackage_atPNewLowering` | Frey-package 64 | C2 |
| Ribet irreducibility/lowering | `Thm_RibetIrr_irreducible_of_point_of_not_dvd`, `Thm_RibetIrr_isFlatAt_of_linearEquiv_baseChange` | 13 | C2 |
| Taylor–Wiles/patching | `Thm_TaylorWiles_exists_isTaylorWilesPrime`, `Thm_CuspForm_heckeLocal_exists_taylorWilesModule_*` | 23 Wiles + 8 TaylorWiles | C1 lifting |
| Heights | Height-named Mathlib-level lemmas | 199 | C3 |

### 6.2 Port priority (A854 order)

1. **P1 — `Thm_FreyPackage_frey_isModular`** (plus `P2M/Sol/S_FreyPackage_frey_isModular` closure): direct C1; closure size NOT yet extracted; extract first.
2. **P2 — lowering/Ribet/Taylor–Wiles**: `Thm_FreyPackage_atPNewLowering`, `Thm_RibetIrr_*` (13), Taylor–Wiles entries (23+8); C2/C1.
3. **P3 — `Thm_CuspForm_*isNewform*` (101) + Heights (199)**: newform and Faltings scaffolding.
4. **P4 — DEFER `ModularCurve` 7,708** (includes Shimura/Cerednik–Drinfeld 28 + 750 QM/fake EC and the δ language): too large relative to direct C need; do not port now.

### 6.3 Closure-size tracking

| target | closure/matches | state |
|---|---|---|
| `frey_isModular` | unknown (P2M/Sol closure not extracted) | BLOCKER: extract import closure before estimate |
| `atPNewLowering` | Frey-package 64 file matches | pending closure extraction (v4.33.1->v4.32.2) |
| RibetIrr | 13 | pending |
| Taylor–Wiles | 23 Wiles + 8 TaylorWiles | pending |
| newform | 101 (+ CuspForm 436, Hecke 179) | pending |
| Heights | 199 | pending closure filter |
| Shimura/Cerednik–Drinfeld | 28 Shimura + 750 QM/fake EC | deferred (P4) |
| ModularCurve | 7,708 | DEFERRED (P4) |
| AutomorphicForm | 2,338 | DEFERRED (large background) |

### 6.4 Updated verdict

- Stage4 gives a concrete unblock path for **newform and Faltings** (P3) and for the arithmetic C1/C2 side (P1/P2).
- **Shimura is present but P4-deferred** inside ModularCurve 7,708; **δ has no dedicated anthro target**; **Néron/Petersson have only definitions/integrand** — these three remain the least covered of the six.
- All anthro entries are 0 compiled and v4.33.1; port priority 1 must first extract the `frey_isModular` closure and mechanically adapt toolchain, then gate `#print axioms` to detect the `p2m_exact_reverting`/hidden-axiom risk.


## 7. A863 latest greens and remaining C-route gaps

All seven files have `olean=True`. They are interfaces/arithmetic shells; the open mathematical content is unchanged unless stated.

| new green | what it closes | what remains |
|---|---|---|
| `Mzk1CRouteAssemblyActual` (`abcConjecture_of_routeC`, `CRouteAssemblyInput`) | assembly shell connecting Frey/modularity/height/E7 to `ABCConjecture` | `E7_radicalBound` and `hE7` are explicit ABC-strength hypotheses; ABC gate NOT passed |
| `Mzk1E7ReductionActual` (`E7Data`, `e7_equiv_chain`, `frey_dictionary_logq/logdf`) | logical equivalence chain + frozen E7 interface | four component Props (`faltingsUpperBound`, `peterssonIdentity`, `neronPeriodLowerBound`, `optimalQuotient`) not proved |
| `Mzk1DExactLowerActual` (L1–L6 defs, `DExactLowerTarget`, exception table) | L1–L6 arithmetic + L7 target definition | L7 geometric lower bound `D_exact >= (1-1/l) log p` still open; exception `e_p` values external (`none`) |
| `Mzk1OptimalQuotientActual` (`OptimalQuotient`, `GeometricModularDegree`, `IsOptimal`) | optimal-quotient definition/interface | existence + degree/period relation not proved |
| `Mzk1NeronPeriodBridgeActual` (`NeronPeriodData`, `DegreePeterssonRelation`, `FaltingsHeightVolumeRelation`) | Neron/Petersson/height interface | relations are structure fields, not proved; no period lower bound |
| `Mzk1FreyABCInvariantsActual` (`freyC4_eq`, `freyC6_eq`, `freyDelta_eq_sixteen_mul_sq`, `log_freyDelta_eq`) | Frey invariants/identities green | conductor-radical structure only |
| `Mzk1FreyConductorFinalActual` (`c4_poly_not_dvd`, `freyDeltaNat_eq`, `LocalMultiplicativeData`) | p ∤ 6 c4 divisibility green | Delta/c4 valuations are fields; p=2,3 Ogg–Saito external |

### Remaining gap table (C route)

| gap | current green | still missing |
|---|---|---|
| **L7** `D_exact` lower bound (geometric input) | `DExactLowerTarget` + L1–L6 arithmetic | prove L7; no geometric input yet |
| **E7 four components** | E7 equivalence chain + interfaces | Faltings bound, Petersson identity/asymptotic, Neron period lower bound, optimal-quotient existence/degree relation |
| **Frey dictionary two equations** | `FreyLogDictionary` def; `frey_dictionary_logq/logdf` re-exports | prove `logq=2logdelta`, `logdf=logN` from geometry |
| **Frey conductor rad** | `FreyConductorRadical`; `c4_poly_not_dvd`; `freyDeltaNat_eq` | prove `N=rad(abc)` and local `ord_p(N)=1`; p=2,3 external |
| **Frey valuations** | `LocalMultiplicativeData` fields | arithmetic bridge to `padicValNat`/Weierstrass invariants; v2/v3 external |

Status of the six components after A863:

- newform: language only (anthro `isNewform` still unported); no new green.
- Shimura: definitions only; no new green.
- δ: `ModularParameterizationDegree`/`E7Statement`/assembly shell green; geometric degree + RT formula still open.
- Faltings: `FaltingsHeightData` + `NeronPeriodData` interfaces green; no height bound.
- Néron: `NeronPeriodData` interface green; no period lower bound.
- Petersson: `peterssonNormOn`/`DegreePeterssonRelation` interface green; no asymptotic.
- optimal quotient: `OptimalQuotient` definition green; existence/degree relation open.
