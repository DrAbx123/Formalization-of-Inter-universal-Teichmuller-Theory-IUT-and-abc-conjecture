# E7-GAP — Eδ component map (modularity/height gap)

## 0. Two numbering schemes (label-conflict fix)

- **Eδ** = this file: the six-component modularity/height gap formerly called "E7". Use `Eδ1`–`Eδ6` below.
- **EMO** = the external Mestre–Oesterlé 1989 input formerly called "E7" in `FLT-PORT-EVIDENCE-AUDIT.md` (prime-conductor exponents). It is **not** one of the six components here.
- Other external references are written `EXT-*` (RT, deg, Petersson, Neron, Faltings, optimal quotient) to avoid further collisions.

Scope: the package needed to turn a modular parameterization into a height/discriminant comparison usable by the C-route Szpiro6 bridge. Status: 2026-11-12, no green theorem claimed.

## 1. Component table

| id | component | external already proved (cite) | our formalization status | open point |
|---|---|---|---|---|
| **Eδ1** | Ribet–Takahashi ratio | `EXT-RT`: Ribet–Takahashi relation between level-lowering quotient/modular degree and congruence data; citation in `FLT-PORT-EVIDENCE-AUDIT.md` E8 (Takahashi), source still flagged "待核对" | `Mzk1RouteCInternalActual.ribetTakahashiDelta (N_E N_f) := N_E / N_f` = **DEF only**; no theorem; olean absent. **Interface freezing in progress.** | exact RT formula, normalization, integrality, and relation to geometric degree/height are unproved; current object is data-level |
| **Eδ2** | deg formula | `EXT-DEG`: classical modular degree/optimal-quotient degree formula (Mazur/Ribet/Takahashi); exact external statement not yet fixed | `ModularParameterizationDegree` (level/degree/isogeny Prop) = **DEF only**; `IsogenyDegreeData` = data-only; **interface freezing in progress** | no `deg(X0(N) -> E)` geometric definition; no formula linking degree to level/congruence/Petersson; no olean |
| **Eδ3** | Petersson asymptotic | `EXT-PET`: classical Petersson inner-product/norm estimates; exact asymptotic citation not fixed | Mathlib `ModularForms/Petersson.lean` green (`petersson` integrand); `peterssonNormOn` DEF + `peterssonIntegrand_nonneg` (if compiled); **interface freezing in progress** | no norm estimate/asymptotic; no lower/upper bound for normalized newform; no proof of `log norm f` behavior |
| **Eδ4** | Neron period lower bound | `EXT-NER`: classical complex/p-adic period and Neron-period lower bounds; exact source not fixed | vendor `Heights/ArchimedeanAlgebraicRealization` green; `PeriodPairScaling`; complex period-lattice theory; `EllipticCurves` reduction/Neron-Ogg-Shafarevich not compiled | no Neron period/pairing object; no explicit period lower bound; complex period lattice is not the global Neron period |
| **Eδ5** | Faltings height bound | `EXT-FALT`: Faltings height comparison/bounds (Faltings 1983; standard); exact formula source not fixed | `Heights/Curve/{CondHeight,DivisorHeight,TupleHeight}` green; `Heights/SilvermanHeight` **NOT compiled** and explicitly says it does not prove Arakelov/Faltings; `FaltingsHeightData` = formula-field data only; **interface freezing in progress** | no constructed Faltings height, no Arakelov metric/period integration, no comparison to naive height; no olean |
| **Eδ6** | optimal quotient existence | `EXT-OQ`: optimal/strong optimal quotient existence (Mazur/Ribet/Takahashi); exact external statement not fixed | **DEFINITION IN PROGRESS** (owner abc); no `OptimalQuotient` in the repo yet; `RibetLoweringHypothesis` is still a trivial placeholder (`0 < N_E -> 0 < N_f -> True`) | definition/existence, plus degree/period relation, still missing; first target is the definition itself |

## 2. Current status update (A860)

- **OptimalQuotient definition in progress** (Eδ6); no mathematical object yet, placeholder must not be cited.
- **Interface freezing in progress** for `ribetTakahashiDelta`, `ModularParameterizationDegree`, `FaltingsHeightData`, `peterssonNormOn`; `Mzk1RouteCInternalActual`/`Mzk1ClassCInterfacesActual` exist but have no oleans yet.
- `Heights/SilvermanHeight` remains uncompiled and explicitly not Arakelov/Faltings; vendor period lane remains partial.
- No gap is discharged by the status update.

## 3. Where exactly is the Eδ gap? (final draft)

1. **Not in the final real-arithmetic bridge.** `Mzk1RouteCInternalActual.szpiro6_of_routeC` already proves `PastenDeltaBound + FreyLogDictionary => Szpiro6Shape` (2C); `Szpiro6Shape` and `ssIneqExplicit_to_szpiro6` are green conditional bridges.
2. **Not in the Frey discriminant identity.** `freyDisc a b c = 16*(a*b*c)^2` is exact (`rfl`); `FreyData.conductor_isRadical` is data only.
3. **The gap is the height comparison formula**, i.e. the missing implication:

   `Eδ1 (RT/deg) + Eδ3 (Petersson asymptotic) + Eδ4 (Neron period lower bound) + Eδ5 (Faltings height bound) + Eδ6 (optimal quotient existence)`
   `=> h(E) = (1/2) log(delta) - log(norm f) + O(1)`
   `=> log delta <= (2+eps) log N + C` (delta bound).

4. **If Pasten is accepted**, the delta bound is an explicit external hypothesis, and Eδ narrows to the **height formula/dictionary** plus Eδ3–Eδ6; the Szpiro arithmetic is already conditionally available. If Pasten is not accepted, the general-N delta bound itself remains open and is the primary open point.
5. **Hard open points**: Eδ1 exact RT/deg formula and Eδ3–Eδ5 analytic estimates. **First executable step** is only interface-level: freeze/compile Eδ1/Eδ2/Eδ5/Eδ3 definitions, prove the Frey log dictionary `logq = 2 log delta`, `logdf = log N`; Eδ6 definition is in progress.

## 4. External citations / caveats

- EXT-RT: Ribet–Takahashi; see `FLT-PORT-EVIDENCE-AUDIT.md` E8; source still flagged "待核对".
- EMO (separate): Mestre–Oesterlé 1989, J. Reine Angew. Math. 400, 173–184; used only by §12.2 prime-conductor arithmetic, not by Eδ.
- EXT-FALT: Faltings 1983 and standard comparison; exact formula source not yet fixed.
- EXT-DEG / EXT-PET / EXT-NER / EXT-OQ: classical results, but citations have not been line-by-line verified in this session; do not treat as machine-checked.
- No port source is evidence; FLT271/anthro are 0 compiled and contain sorry/axiom as recorded elsewhere.


## 5. A863 status update (current; supersedes the per-row statuses in §1)

`Mzk1E7ReductionActual` is now GREEN and freezes the E7 interface. The equivalence chain is logical wiring only; the four `jointPackage` component Props are still content gaps.

| id | current green | still missing |
|---|---|---|
| Eδ1 Ribet–Takahashi | `Mzk1RouteCInternalActual.ribetTakahashiDelta` DEF; `Mzk1E7ReductionActual.frey_dictionary_logq/logdf` re-export | exact RT formula, normalization, integrality; no theorem |
| Eδ2 deg formula | `ModularParameterizationDegree` DEF; `Mzk1E7ReductionActual.E7Statement`/`E7GapStatement` wire | geometric `deg(X0(N)->E)` and degree formula |
| Eδ3 Petersson asymptotic | `peterssonNormOn` DEF + nonneg; `NeronPeriodData.peterssonNormSq` field | Petersson identity/asymptotic/norm estimate |
| Eδ4 Neron period lower bound | `NeronPeriodData` interface (`period`, `covolume`, `volE_pos`) | existence + explicit lower bound |
| Eδ5 Faltings height bound | `FaltingsHeightData`; `NeronPeriodData.FaltingsHeightVolumeRelation` field | constructed Faltings height + bound/comparison |
| Eδ6 optimal quotient existence | `Mzk1OptimalQuotientActual.OptimalQuotient` DEFINED (green); `GeometricModularDegree` | existence + degree/period relation |

### Remaining gap table (A863)

| gap | green now | still missing |
|---|---|---|
| **L7** `D_exact` lower bound (geometric input) | `Mzk1DExactLowerActual.DExactLowerTarget` + L1–L6 arithmetic | prove L7 lower bound |
| **E7 four components** | `e7_equiv_chain` logical wiring; interfaces frozen | Faltings/Petersson/Neron/optimal-quotient content (the four `jointPackage` Props) |
| **Frey dictionary two equations** | `FreyLogDictionary` def; `frey_dictionary_logq/logdf` re-exports | prove `logq=2logdelta`, `logdf=logN` from geometry |
| **Frey conductor rad** | `FreyConductorRadical`; `c4_poly_not_dvd`; `freyDeltaNat_eq` | prove `N=rad(abc)` + local `ord_p(N)=1`; p=2,3 external |
| **Frey valuations** | `LocalMultiplicativeData` fields; `c4_poly_not_dvd` | arithmetic bridge to `padicValNat`/Weierstrass invariants; v2/v3 external |

### Final Eδ conclusion after A863

The Eδ gap is now localized precisely to:

`jointPackage D := D.faltingsUpperBound ∧ D.peterssonIdentity ∧ D.neronPeriodLowerBound ∧ D.optimalQuotient`

plus the **L7 geometric lower bound** and the **Frey dictionary/conductor/valuation** rows. The assembly shell `Mzk1CRouteAssemblyActual.abcConjecture_of_routeC` is green but still takes `hE7 : (∃ Cprime, Szpiro6Shape logq logdf Cprime) -> ABCConjecture` as an explicit hypothesis; it does not prove E7 and the ABC gate is NOT passed.

No gap is discharged by A863; the seven files are interface/wiring/arithmetic greens.
