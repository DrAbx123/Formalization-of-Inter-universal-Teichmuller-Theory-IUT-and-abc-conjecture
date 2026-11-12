# OUR-GAPS — C-route: external citations vs our missing work

Scope: **C route only** (Frey / modularity / height). IUT/Step-XI is separate. This is a gap plan, not a proof claim. Updated 2026-11-12; status/owners refreshed at A858.

## 0. Chain

`ABC triple` -> `Frey curve + invariants` -> `modularity` -> `newform + Ribet lowering` -> `δ = deg(X0(N) -> E)` -> `height / Petersson / conductor dictionary` -> `bound => Szpiro6Shape` -> `ABCConjecture`.

## 1. Two columns

| External already proved (cite, do not port) | Our missing work |
|---|---|
| E1 Frey formulas / discriminant / conductor (classical) | **G1** ABC-triple Frey bundle + invariants (semistability/minimality/bad-prime/rho linkage) |
| E2 Wiles 1995 + Taylor-Wiles; BCDT 2001 semistable modularity | **G2** delta definition + delta bound (geometric; general N open; Pasten external if accepted) |
| E3 Ribet 1990 level lowering | **G3** height/conductor dictionary (Faltings height + Petersson norm + logq=2logdelta, logdf=logN) |
| E4 Mazur 1977/1978 torsion/prime-isogeny | **G4** external assumptions => Szpiro6Shape bridge + constants |
| E5 Mestre-Oesterle 1989 prime-conductor exponents | **G5** section 12.2 prime-conductor internal arithmetic |
| E6 Faltings height / Ribet-Takahashi formula | **G6** final assembly to ABCConjecture |
| E7 Pasten 2018 / 2026-09 delta bound (external only if accepted; general N open) | Port sources are not evidence (FLT271/anthro 0 compiled; sorry/axiom) |

## 2. Six gaps: owner / status / next executable step

### G1 - ABC-triple Frey construction and invariants
- **Target**: `def freyCurveOfABCTriple (h : IsABCTriple a b c) : WeierstrassCurve Rat`; `structure ABCFreyPackage` bundling `E`, discriminant `16*(a*b*c)^2`, `N = rad(a*b*c)`, minimal discriminant, semistability, bad-prime set, `c4/c6/j`, and the p-torsion representation.
- **Status**: **IN PROGRESS (owner hull)**. Frey invariants are GREEN: `Geometry/FreyWeierstrassCurve.rationalFreyWeierstrassCurve`, `freyWeierstrassCurve_discriminant_square`, `rationalFreyWeierstrassCurve_discriminant_of_isABCTriple`; `FreyDiscriminantRadical.rationalFreyWeierstrassCurve_discriminant_natCast_sixteen_mul_sq_of_isABCTriple`; `FreyConductorOdd/TwoAdic`; `FreyOddReduction`, `FreySplitMultiplicativeReduction`, `FreyTwoTorsion`, `FreySplittingFields`. Remaining: conductor formula for `p ∤ 6` (in progress), bundled `ABCFreyPackage`, minimality/semistability linkage, rho-bar construction. `FreyWeierstrassCurve` doc still says it does not establish minimality/semistability/conductor formulas.
- **Owner**: `hull`.
- **Next executable step**: finish the `p ∤ 6` conductor lemma (green target), then write `LeanFormal/IUT/ABCBridge/Geometry/ABCFreyPackage.lean` filling fields from the existing greens; gate single-file + `#print axioms`.

### G2 - delta definition and delta bound
- **Target**: `def ModularParameterizationDegree (E : WeierstrassCurve Rat) : Nat`; `def RibetTakahashiDelta (E f) : Rat := N_E / N_f`; `def ModularityDegreeBound (logDelta logN C eps : Real) : Prop := logDelta <= (2+eps)*logN + C`.
- **Status**: **IN PROGRESS (owner abc)**. Definition of δ is being frozen; only abstract real predicate `Mzk1ModularityBridgeActual.ModularityDegreeBound` and conditional bridge `modularityDeltaBound_to_szpiro6` exist; no `X0(N) -> E` geometric degree. General N bound open; Pasten external if accepted.
- **Owner**: `abc`.
- **Next executable step**: finish the δ definition + `ModularityDegreeBound` statement and connect to `Mzk1ModularityBridgeActual.modularityDeltaBound_to_szpiro6`; keep Pasten as explicit named hypothesis.

### G3 - height / conductor dictionary
- **Target**: `def FaltingsHeight (E) : Real`; `def PeterssonNorm (f) : Real`; formula `h(E) = (1/2)*log(delta) - log(norm f) + O(1)`; dictionary `logq = 2*log(delta)`, `logdf = log N`, `N = rad(abc)`.
- **Status**: **IN PROGRESS (owner abc)**. Green: `ABCEllipticHeightCriterion.abcConjecture_iff_freyJDenominatorHeightCriterion`, `..._iff_freyJProductHeightCriterion`, `..._iff_legendreJDenominatorHeightCriterion`; `FreyOddConductorHeightCriterion.freyJDenominatorHeightCriterion_iff_freyOddConductorHeightCriterion`; `ABCModelHeightComparison.rationalFreyWeierstrassCurve_j_height_bounds`; `Heights` curve/divisor heights. Remaining: Faltings height (vendor `Heights/SilvermanHeight` not compiled and explicitly not Arakelov/Faltings), Petersson norm, exact formula/dictionary; `Mzk1FinalBoundarySzpiroActual.remainingDictionaryGaps` marks the log-volume identifications PENDING.
- **Owner**: `abc`.
- **Next executable step**: compile `Heights/SilvermanHeight.lean` (remaining 8) + `ArchimedeanAlgebraicRealization`; expose `FaltingsHeight`; state conductor dictionary `logdf = log N` against `FreyConductorOdd`; gate axioms.

### G4 - external assumptions => Szpiro6Shape bridge and constants
- **Target**: `theorem modularity_bound_to_szpiro6` / `szpiro6_of_delta_height_bound`, consuming E2/E3/E6 and producing `Szpiro6Shape logq logdf Cprime`.
- **Status**: **IN PROGRESS (owner abc)**. Green arithmetic: `Mzk1FinalBoundarySzpiroActual.Szpiro6Shape`, `ssIneqExplicit_to_szpiro6` (needs `V <= (1/4)*l*logdf + C0`), `szpiro6_to_ssIneqExplicit`; `Mzk1ModularityBridgeActual.modularityDeltaBound_to_szpiro6` (file exists; olean currently absent; condition `logq=2logdelta`, `logdf=logN`); `Mzk1ShellCoeffComputationActual.cVModel_eq` (c_V=1/4). Remaining: arithmetic identifications and exact hull upper bound; explicit Cprime/C0.
- **Owner**: `abc`.
- **Next executable step**: build olean for `Mzk1ModularityBridgeActual.lean`; prove `logq=2*logdelta` and `logdf=logN` as separate arithmetic lemmas from G1/G3; combine with `ssIneqExplicit_to_szpiro6`; track Cprime explicitly.

### G5 - section 12.2 prime-conductor internal arithmetic
- **Target**: `structure PrimeConductorCurve`; `def MestreOesterleBound : Prop`; `T(l) = 6*l*(l+5)/((l+4)*(l-3))`; `theorem five_le_T_one_sub_inv`, `e_le_T_one_sub_inv`, `paperGap_of_primeConductor`.
- **Status**: **IN PROGRESS (owner shehdd)**. Green skeleton: `Mzk1PrimeConductorRouteActual` (EXIT=0, olean=True) proves `five_le_T_one_sub_inv`, `e_le_T_one_sub_inv`, `paperGap_of_primeConductor_arith`, `ssIneqExplicit_of_paperGap`, `paperGap_of_primeConductor` (conditional on external `MestreOesterleBound` and `D_exact >= (1-1/l)*log p`). In progress: the concrete `D_exact` targets (L1-L7) and the exception table for p=11,17,19,37; Theta-data legality still pending.
- **Owner**: `shehdd`.
- **Next executable step**: land the L1-L7 `D_exact` target lemmas + exception-table numeric certificate; keep `MestreOesterleBound` as explicit external hypothesis.

### G6 - final assembly to ABCConjecture
- **Target**: `theorem abcConjecture_of_C_route` assembling G1-G5 to `ABCConjecture`.
- **Status**: **IN PROGRESS (owner mainline)**. Assembly shell exists: `ABCFrontier.abcConjecture_of_frontier`, `abcFrontier_iff_abcConjecture`; `Cor312ToABCBridgeInterface.cor312ToABCBridgeInterface_nonempty_iff_abcConjecture`; `ABCEllipticHeightCriterion` equivalences. Remaining: actual C-route inputs; all paths conditional on unproved frontier/height packages; no unconditional `ABCConjecture`.
- **Owner**: `mainline`.
- **Next executable step**: finish `Mzk1CRouteAssemblyActual.lean` shell taking G1-G5 as explicit named hypotheses and deriving `ABCConjecture` via `ABCFrontier`/height-criterion equivalences; gate trio.

## 3. Port dependency backlog (background queue)

Not evidence. Ordered by C-route value; queue them only after the C-route gap interfaces are frozen.

| order | source | files | compiled | component | first-error risk |
|---|---|---|---|---|---|
| 1 | Mathlib ModularForms | 19 | 38 oleans (100%) | base CuspForm/qExpansion/discriminant/petersson integrand | none (green) |
| 2 | anthro Definitions | 1450 | 0 | language: Def_ModularCurve 291, Def_AutomorphicForm 106, Def_CuspForm 32, Def_Hecke 10, Def_ModularForm 5 | v4.33.1 -> v4.32.2: unknown module/identifier |
| 3 | FLT271 | 271 | 0 | Frey/Galois/patching/level lowering (Patching 14 = 7 顶层 + 7 Utils, import 闭包 19) | v4.35.0 drift; **70 sorry / 3 axiom declarations** (stage4 A868), not evidence |
| 4 | Heights remaining | 8 | 56/64 | Faltings/height scaffold | missing import/typeclass in period integration |
| 5 | anthro Shimura/Cerednik | 28 + 750 | 0 | Shimura curves/QM | deferred with ModularCurve 7708 |
| 6 | flt-regular | 25 | 0 | regular-prime FLT only | v4.36.0-rc2 drift; low value |
| 7 | FLT ported remaining | 117 | 14/131 | scaffolding | sorry/axiom; not evidence |

## 4. External citations (cite, do not port)

- E1 classical Frey curve formulas (Frey/Serre): cite.
- E2 A. Wiles, Ann. of Math. 141 (1995) 443-551; Taylor-Wiles; Breuil-Conrad-Diamond-Taylor (2001) semistable case: cite.
- E3 K. Ribet, Invent. Math. 100 (1990) 431-476: cite.
- E4 B. Mazur, Publ. Math. IHES 47 (1977) 33-186; Invent. Math. 44 (1978) 129-162: cite.
- E5 J.-F. Mestre, J. Oesterle, J. Reine Angew. Math. 400 (1989) 173-184: cite.
- E6 Faltings height / Ribet-Takahashi formula: cite.
- E7 H. Pasten, Shimura curves and the abc conjecture (2018; 2026-09 preprint): external only if accepted; general N open.

## 5. Discipline

- FLT271 (271 files, 0 compiled, **70 sorry / 3 axiom declarations**) and anthro Definitions (1450 files, 0 compiled, v4.33.1) are port sources, not green evidence.
- Do not cite ported `Thm_*` wrappers until compiled and `#print axioms`-gated; the real work is in the `P2M/Sol` closure.
- No new axiom/sorry/True/PUnit; external theorems stay explicit hypotheses.


## 6. Owner/status snapshot (A858)

| gap | owner | current status | next executable step |
|---|---|---|---|
| G1 Frey/invariants | **hull** | invariants GREEN; conductor `p ∤ 6` in progress; bundle/minimality/rho pending | finish `p ∤ 6` conductor; write `ABCFreyPackage.lean` |
| G2 delta definition/bound | **abc** | definition being frozen; abstract `ModularityDegreeBound` only | freeze `ModularParameterizationDegree`/`RibetTakahashiDelta`; Pasten external hypothesis |
| G3 height/conductor dictionary | **abc** | height-criterion equivalences GREEN; Faltings/Petersson/dictionary pending | compile `SilvermanHeight`; expose `FaltingsHeight`; prove `logdf=logN` |
| G4 external => Szpiro6 bridge/constants | **abc** | real-arithmetic bridge conditional GREEN; identifications/Cprime pending | build olean; prove `logq=2logdelta`, `logdf=logN`; combine with `ssIneqExplicit_to_szpiro6` |
| G5 section 12.2 arithmetic | **shehdd** | green skeleton; `D_exact` targets + exception table in progress | land L1-L7 + exception numeric certificate for 11/17/19/37 |
| G6 final assembly | **mainline** | assembly shell GREEN/conditional | finish `Mzk1CRouteAssemblyActual.lean` shell with G1-G5 as hypotheses |

Note: owner reassignment only; no gap is discharged by this status update. The six sections above remain the authoritative target/evidence text.
