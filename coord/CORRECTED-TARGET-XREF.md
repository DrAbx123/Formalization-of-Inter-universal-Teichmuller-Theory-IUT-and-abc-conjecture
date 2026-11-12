# CORRECTED-TARGET CROSS-REFERENCE / DEPRECATION INVENTORY

**Status:** fact-only work product under gate freeze (Lead assignment; mainline A277-A281).
**Authoritative gate status:** **NOT PASSED**. The full gate path is **invalid as constructed**
(A277: partial_induction base/stepExists unconditional+lossy; comp ratFunc product unsound;
`Mzk1Lemma24Goal` degenerate = `beta ∉ S`; thm25_wiring uses hcore only with free Prop fields
in GeometricCoreWitness; UnramifiedOver stated on Q-points vs paper C-points).
**Freeze:** no gate-table edits, no republish/FINAL ROWS until a restated target + real consumer
exists. This document does not change any Lean file and is not evidence.
**Vocabulary fixed (A281/S3246):** `P1Point Q` (= `Option Q`) for P^1(Q); CV as `Set (P1Point C)`
(C-point values); `specialSet = {infinity, 0, 1}`.
**Companion document:** `coord/OLD-TARGET-CONSUMERS-ANALYSIS.md` (mainline A282): deprecated symbols -> consumers -> needed changes; counts 14 `CompositionActual` importers, 22 `Mzk1Lemma24StatementShape` touchers, 12 `partial_induction` files, 7 `Mzk1Lemma24Goal` files. **Bugfix status (A282): #1 DONE — `Mzk1Lemma22CompositionActual.comp` fixed on disk to true substitution composition (checker CITABLE 8 decls, A277 issue#2 resolved); #2 PENDING — `Mzk1Lemma22InductionActual` interface still old (unconditional/lossy partial_induction).**
**Restated reference implementation:** `tmp/sheaf/xif/paper/RestatedLemma24InterfaceActual.lean`
(abc; Lead A280-A281): `Mzk1Lemma24Target`, `CVInvariant`, `Mzk1Lemma24CorrectedStatement`,
`CVCompositionLawStatement`, `SpecialSetPreservationStatement`, `criticalValuesOverC`.

Scope of the sweep: `grep` over `tmp/sheaf/xif/paper/*.lean` for
`Mzk1Lemma24Goal|StepProviderStatement|BaseProviderStatement|Lemma24Shape|targetSet|unramifiedAt`
(240 hits) and `criticalValues|specialSet|CVInvariant|criticalValue|polyEvalP1|criticalPoint`
(177 hits). Gate-table files `IUTExternal3*Gate*.lean` are frozen history and are excluded from
the rewrite action list.

---

## 1. DEPRECATED-UNDER-CORRECTED-TARGET inventory

Legend: **D** = deprecated (do not cite as paper obligation), **R** = reusable mathematical
content (keep, but re-target), **S** = superseded pointer/stub (ignore/delete), **U** = consumer
that must be updated.

### 1.1 Core defective definitions (source of degeneracy)

| file:line | declaration | state | why | restated form / action |
|---|---|---|---|---|
| `Mzk1Lemma24AssemblyActual.lean:20` | `Mzk1Lemma24Goal S β := ∃ targetSet unramifiedAt, Mzk1Lemma24StatementShape ℂ S β targetSet unramifiedAt` | **D** | witness `mapPoints:=id, ratFunc:=0, T:=S, unramifiedAt:=complement T, nonconstant:=True` satisfies shape iff `β ∉ S`; map/ratFunc unlinked; no CV condition | replace with `RestatedLemma24InterfaceActual.Mzk1Lemma24Target` (q∈Q[X], fixed `specialSet`, `criticalValuesOverC q ⊆ {0,1}`, derivative nonzero off {0,1}) or an abstract `CVInvariant` goal |
| `Mzk1Lemma24AssemblyActual.lean:60` | `Mzk1Lemma24StepProviderStatement` | **D** | provider returns `Nonempty (Mzk1Lemma24Step μ st)` whose transport is of the degenerate Goal; no CV invariant, no composition law | restate provider: for `μ st ≠ (0,0)` produce next state + measure decrease + a map/factor that promotes the restated target with `CVCompositionLawStatement` |
| `Mzk1Lemma24AssemblyActual.lean:67` | `Mzk1Lemma24BaseProviderStatement` | **D** | base case into degenerate Goal (`β ∉ S` is trivial) | restate base: rational-case construction into fixed `specialSet` + CV condition (`CVInvariant`); hull rational base provider is the starting point |
| `Mzk1Lemma24AssemblyActual.lean:39` | `mzk1Lemma24_assembly` (wf recursion skeleton) | **R** | recursion principle itself is fine | retarget Goal type to restated target/CV invariant (`hwf.fix` structure reusable) |

### 1.2 Old shape/predicate layer (free targetSet/unramifiedAt)

| file:line | declaration | state | why | restated form / action |
|---|---|---|---|---|
| `Mzk1P1MorphismInterfaceActual.lean:73` | `UnramifiedOver φ T unramifiedAt := ∀p, φ.mapPoints p ∈ T → unramifiedAt p` | **D** for paper use | puts unramifiedness on Q-points via a *free* predicate; paper needs C-point unramifiedness away from {0,1,∞}; predicate carries no content | keep as lightweight helper; paper obligation must use `criticalValuesOverC q ⊆ {0,1}` + derivative condition on C-points |
| `Mzk1P1MorphismInterfaceActual.lean:78` | `Mzk1Lemma22StatementShape` | **D** | free `targetSet`/`unramifiedAt` ⇒ vacuous-able | use `Mzk1Lemma22FullShape` (stage4, specialSet + polyUnramifiedAt) or restated target layer; keep only as interface record |
| `Mzk1P1MorphismInterfaceActual.lean:98` | `Mzk1Lemma24StatementShape K S β targetSet unramifiedAt` | **D** | same defect as Goal (target/unramified data free) | replace by `Mzk1Lemma24Target`; the file `Mzk1Lemma24CorrectedTargetActual.lean` is itself **SUPERSEDED** pointer (see 1.5) |
| `Mzk1Thm25WiringActual.lean:97` | `Lemma24Shape : Prop := ∀ K [Field K] [DecidableEq K] S β targetSet unramifiedAt, Mzk1Lemma24StatementShape K S β targetSet unramifiedAt` | **D** | inherits all defects; cannot be the gate hypothesis | replace with `RestatedLemma24InterfaceActual.Mzk1Lemma24CorrectedStatement` (or consumer-facing restated target); update `Thm25WiringRecord.lemma24` (`Mzk1Thm25WiringActual:112`) |
| `Mzk1Lemma22StepConstructionActual.lean:101-124`; `Mzk1Lemma22CompositionActual.lean:77-92`; `Mzk1Lemma22GChoiceDataActual.lean:53-68`; `Mzk1Lemma22InductionActual.lean:46-66` | `Mzk1Lemma22InductionStep`-family with `targetSet`/`unramifiedAt` fields | **R/D mix** | machinery for Lemma 2.2 shape over free target data; not CV-aware. **A282 update: `CompositionActual.comp` FIXED to true substitution composition (CITABLE 8 decls) — recheck all 14 importers; `partial_induction` (InductionActual:61) still unconditional+lossy (bugfix #2 PENDING)** | keep as historical interface until InductionActual retargeted to phi=gPoly + H-on-image + explicit C-point target; do not use for 2.4/2.2 paper obligation |

### 1.3 Provider/derived files built on the old goal (progress only, not closure)

| file:line | content | state | notes / restated form |
|---|---|---|---|
| `Mzk1Lemma24BaseProviderActual.lean:37` | `∃ φ targetSet, PreservesSet φ S targetSet ∧ AvoidsPoint φ β targetSet` over ℂ | **R/D** | rational base construction reusable as base *building block*; restate conclusion to `CVInvariant`/`Mzk1Lemma24Target` (fixed `specialSet`, CV in {0,1}); do not cite as BaseProvider closure |
| `Mzk1Lemma24BaseCaseActual.lean:18`; `Mzk1Lemma24BaseCaseComplexActual.lean:18` | rational base `∃ φ targetSet ...` over ℚ / ℂ | **R** (BaseCase over ℚ) / **D** (BaseCaseComplex abc-deprecated) | BaseCase over ℚ is a valid reasoning asset; BaseCaseComplex explicitly abc-deprecated and NOT cited (A279); re-target both to restated CV target if reused |
| `Mzk1Lemma24StepProviderActual.lean` | `s3135_criticalPoint_degree_drop` (S1a) + `FieldDegreeDropStatement`/`ValueDegreeDropStatement` class-B named | **R** | S1a is genuine reusable math (minpoly degree drop); statements are numeric layers, not provider closure |
| `Mzk1Lemma24ValueDegreeDropActual.lean` | `valueDegreeDrop_proved`, `fieldDegreeDrop_proved` | **R** | reusable S1b layer; keep, but they feed a *restated* provider, not the old one |
| `Mzk1Lemma24StepProvider2Actual.lean:41-42,64` | transport functions `Mzk1Lemma24Goal Sim (...) → Mzk1Lemma24Goal ...`; status record | **R/D** | `s3135_mOfPoints_lt_of_forall_reducedDegree_lt` (S2) and `s3135_goal_transport` (S3, explicit `Sim`+membership) are reusable transport *techniques*; their Goal type must be restated before citing |
| `Mzk1Lemma24StepProvider3Actual.lean` | `s3135_f0S0_m_lt` (S2-i) | **R (progress only)** | numeric measure-drop piece; keep |
| `Mzk1Lemma24NormalizationTransferActual.lean:74-107` | transfer lemmas over `targetSet`+`unramifiedAt` | **R/D** | transfer *pattern* reusable (P1Morphism comp/conj); restate to CV invariant + specialSet; keep file marked historical interface |
| `Mzk1Lemma24NormalizationTransferVariantActual.lean:44-69` | `Mzk1Lemma24Goal`-level variant | **D** | consumes old Goal; keep as history only |
| `Mzk1Lemma24NormalizationIntegrationActual.lean:28-31` | `∀ unramifiedAt, ∃ targetSet, Mzk1Lemma24StatementShape` | **D** | optional precise-statement stub, explicitly NOT evidence (S3237/S3242); do not cite |
| `Mzk1Lemma24NormalizationDischargeActual.lean` | superseded pointer stub (502B, two rfl lines) | **S** | NOT evidence; ignore red probe |
| `Mzk1Lemma24ShapeStepActual.lean:27-30` | `∃ φ targetSet, PreservesSet φ (image f0) targetSet ∧ AvoidsPoint ...` | **R/D** | step-map construction is genuine; `targetSet` free ⇒ restate target as fixed `specialSet` + CV condition |
| `Mzk1Lemma24StatementShapeActual.lean:28-38` | shape theorem with free `unramifiedAt` input | **D** | old-layer consumer; restate via `Mzk1Lemma24Target` |
| `Mzk1Lemma24MainStatementActual.lean` | `s3135_belyi_polynomial_of_finiteSet` (Belyification via ported TauCeti) + `s3135_mainReduction_shape_partial` | **R/D** | Belyification existence is a genuine asset (ported, Apache-2.0); `mainReduction_shape_partial` is old-shape ⇒ restate |
| `Mzk1Lemma24P1ApplicationActual.lean:22-25` | `∃ φ targetSet ...` (Belyi P1 application) | **R/D** | construction reusable; conclusion must be restated (CV in {0,1}) |
| `Mzk1Lemma24WiringActual.lean`; `Mzk1Lemma24BelyiConsumeActual.lean`; `Mzk1Lemma24GrowthActual.lean`; `Mzk1Lemma24BetaAvoidanceActual.lean`; `Mzk1Lemma24F0BoundActual.lean`; `Mzk1Lemma24DescentActual.lean`; `Mzk1Lemma24Descent2Actual.lean`; GaloisUnion/Union/ConjInvariance/Measure/Proof/Proof2 | numeric/analytic foundations (Vieta bound, descent, Galois, measure, beta-avoidance) | **R** | genuine reusable pieces; keep; they do not close the restated target by themselves |
| `Mzk1Lemma24CorrectedTargetActual.lean` | earlier corrected-target draft | **S** | SUPERSEDED by `RestatedLemma24InterfaceActual` (A280); not evidence |

### 1.4 Consumers/adapters that must be updated (D/U)

| file:line | what | action |
|---|---|---|
| `Mzk1Thm25WiringActual.lean:112,124,139,148` | `lemma24 : Lemma24Shape` named hypothesis; wiring records | **D** gate hypothesis; replace with restated target field; do not cite wiring as binding (A277: conclusion uses hcore only; GeometricCoreWitness free Prop fields) |
| `Mzk1Thm25ConsumerActual.lean:14,57,70` | consumer with `h24 : Lemma24Shape` | **U**: update to restated target; keep as interface record only |
| `Mzk1Thm25UnconditionalActual.lean:55,64` | `h24 : Lemma24Shape` unconditional path | **D** old gate path; must not be cited as "Thm2.5 unconditional" (A277) |
| `Hull11H6Mzk1UpgradeActual.lean:27,67,93` | `h24 : Lemma24Shape` in hull H6 upgrade | **U/D**: H6 remains PARTIAL; re-target h24 to restated target before any upgrade |
| `Mzk1Thm25P1CompositeConsumerDesignActual.lean:42,96` | `specialSetC` design + P1 vocabulary | **U**: align to fixed vocabulary. **A301/S3254 RE-VERIFIED: CITABLE 12 decls, src 8098B sha 90638394 / olean C7845001 (probe _Mzk1P1CompositeDesignProbe 1083B EXIT=0 probe_ok TRUE) — STATEMENT/DESIGN ONLY, no closure; `P1CompositeRealConsumerTarget` = C-point version (f preserves S into specialSet {∞,0,1}, avoids β, `CPointCriticalValuesIn01` = C-strengthened Lemma 2.1(b)); `P1CompositeConsumerInputs/Statement` name exact upstream needs; hullInterfaceNeeds 6; availableMoebiusAssets 8. **A305 layering correction: local MoebiusData = Q-typed source layer; qpilot extension separate; C-file distinct C-typed variant; no cycle/dup deletion; design re-verified WITH probe EXIT0 8715 CITABLE 12 (src 90123C46/olean AC95FFC6)** |
| `Mzk1Lemma22FullGateActual.lean`; `Mzk1Lemma22FullShapeHelpersActual.lean`; `Mzk1Lemma22StatementShapeActual.lean` | full-shape 2.2 files (specialSet, polyUnramifiedAt, CV helpers, `criticalValues_comp_subset` use) | **R** for CV composition/helper content; these use their own 2.2 target, not the old 2.4 Goal; keep, reference as CV bridge material |
| Audit records `S3232/S3233/S3235/S3236/S3240/S3241/S3242/S3243/S3221/S3222/S3217` etc. | claims of "residues closed"/"2.4 COMPLETE" under old target | **historical**: mark as progress-only; do not cite as paper closure (S3244 supersedes; S3246 assignment record) |

### 1.5 Superseded/pointer files (S)

- `Mzk1Lemma24CorrectedTargetActual.lean` (superseded by RestatedLemma24InterfaceActual).
- `Mzk1Lemma24NormalizationDischargeActual.lean` (superseded pointer stub, not evidence).
- `Mzk1Lemma24NormalizationIntegrationActual.lean` (optional precise statement; not evidence).
- `Mzk1Lemma24BaseCaseComplexActual.lean` (abc-deprecated per Lead/A279; not cited).

---

## 2. RESTATED FORM — canonical replacement mapping

From `RestatedLemma24InterfaceActual.lean` (C-point version; Lead A280/A281):

- `specialSet (K) := {P1Point.infty, P1Point.ofFinite 0, P1Point.ofFinite 1} : Set (P1Point K)`
- `polyEvalP1 (q : Polynomial ℚ) : P1Point ℚ → P1Point ℚ := fun p => p.map (fun x => Polynomial.eval x q)`
  (so `∞ ↦ ∞`)
- `criticalValuesOverC (q : Polynomial ℚ) : Set ℂ := {c | ∃ z : ℂ, aeval z q' = 0 ∧ aeval z q = c}`
- **`Mzk1Lemma24Target (S : Finset (P1Point ℚ)) (β : P1Point ℚ) : Prop** :=
  `∃ q : Polynomial ℚ, 0 < q.natDegree ∧ (∀ p ∈ S, polyEvalP1 q p ∈ specialSet ℚ) ∧
   polyEvalP1 q β ∉ specialSet ℚ ∧ criticalValuesOverC q ⊆ ({0,1} : Set ℂ) ∧
   (∀ z : ℂ, aeval z q ∉ ({0,1} : Set ℂ) → aeval z q' ≠ 0)`
- `CVInvariant S q` := nonconstant ∧ q(S) ⊆ specialSet ∧ CV(q) ⊆ {0,1}
- `Mzk1Lemma24CorrectedStatement` := ∀ S β, β ∉ S → `Mzk1Lemma24Target S β`
- `CVCompositionLawStatement` := `CV(r.comp q) ⊆ r '' CV(q) ∪ CV(r)`
- `SpecialSetPreservationStatement` := companion for r keeping {0,1} in itself

**Per-item replacement:**

1. `Mzk1Lemma24Goal S β` → `Mzk1Lemma24Target S β` (for fixed rational target), or abstract
   `CVInvariant`-based goal when composing intermediate factors.
2. `Mzk1Lemma24StepProviderStatement` → provider: `μ st ≠ (0,0)` ⇒ next state + measure decrease
   + factor `r` such that `CVInvariant next.1 q_next` implies the target at `st` using
   `polyEvalP1`/composition law; no free `unramifiedAt` predicate.
3. `Mzk1Lemma24BaseProviderStatement` → rational base: explicit `q = (2/D)·∏(X−s)` style
   construction mapped into `specialSet` (ℚ then base-change to C) with `CV(q) ⊆ {0,1}`.
4. `Lemma24Shape` (Thm25 wiring hypothesis) → `Mzk1Lemma24CorrectedStatement` (or its
   consumer-facing C-point form); wiring must expose the restated target as *the* hypothesis.
5. `Mzk1Lemma24StatementShape K S β targetSet unramifiedAt` → `Mzk1Lemma24Target S β`
   (Q-rational S/β + C-point CV); no arbitrary target/unramified data.

---

## 3. CV VOCABULARY CORRESPONDENCE / BRIDGE TABLE

Fixed vocabulary (S3246): `P1Point Q` + CV `Set (P1Point C)`; `specialSet = {0,1,inf}`.

| layer | current definitions in tree | restated target vocabulary | bridge needed |
|---|---|---|---|
| P^1 model | `P1Point K := Option K`; `P1Point.infty := none`; `P1Point.ofFinite := some` (`Mzk1P1MorphismInterfaceActual.lean:38-58`) | `P1Point ℚ` for S/β; `P1Point ℂ` for C-point CV | identity (abbrev); no structural bridge needed; ensure `DecidableEq` uses |
| special target | old free `targetSet`; 2.2 files use `specialSet` local defs (`Mzk1PolyMapActual.lean:48`, `Mzk1Lemma22FullGateActual.lean` specialSet membership) | `specialSet ℚ = {∞,0,1}` fixed; `specialSet ℂ` for C-point values | unify local `specialSet` defs to `RestatedLemma24InterfaceActual.specialSet` (or one shared def); avoid duplicating |
| CV (def) | `Polynomial.criticalValues L` (rootSet of derivative mapped by q; ported TauCeti `criticalValues_def/mem_criticalValues`; `belyi_criticalValues_subset` gives CV over ℚ ⊆ {0,1}) | `criticalValuesOverC q : Set ℂ` (aeval at roots of q') | prove/record: for `q : Polynomial ℚ`, `criticalValuesOverC q` is the base-change of `q.criticalValues ℚ`; bridge lemma needed if mixing |
| CV values domain | old layer: CV not represented at all (only free `unramifiedAt` predicate); 2.2 helpers: `criticalValues ℂ` subsets via `Polynomial.criticalValues_comp_subset` (`Mzk1Lemma22FullShapeHelpersActual.lean:45-53`) | CV values as elements of `Set ℂ` i.e. `{0,1}`; also `Set (P1Point ℂ)` when finite points embedded | bridge `Set ℂ ↔ Set (P1Point ℂ)` via `ofFinite` image; infinity is never a CV value (q finite at ∞? q(∞)=∞) — document |
| unramifiedness | `UnramifiedOver φ T unramifiedAt := ∀ p, mapPoints p ∈ T → unramifiedAt p` (Q-points predicate) | C-point condition: `∀ z : ℂ, aeval z q ∉ {0,1} → aeval z q' ≠ 0` | **Q→C bridge**: old predicate must be replaced by derivative condition on C-points; Q-vs-C gap is a WEAKNESS (A277). Need lemma: if CV over ℂ ⊆ {0,1} and derivative nonzero off {0,1} then unramified away from {0,1}; and `polyUnramifiedAt` (2.2, derivative roots over ℚ) is only a ℚ-level witness |
| composition | old transport composes `P1Morphism` via `ratFunc` product (A277 unsound as used; **A282 fixed to true substitution composition**); 2.2 helper instantiates `Polynomial.criticalValues_comp_subset` at ℂ | `CVCompositionLawStatement`: `CV(r∘q) ⊆ r '' CV(q) ∪ CV(r)`; `SpecialSetPreservationStatement` for special set | **PROVED (S3255 RestatedLemma24CVLaw CITABLE 9EE41ECD): `CVCompositionLawStatement` + `SpecialSetPreservationStatement` + `criticalValuesOverC_eq` (C-point CV = ported TauCeti criticalValues ℂ) + CVCompat; discharges CV-accounting hypotheses of `s3135_CVInvariant_comp`** |
| infinity handling | old shape handles ∞ via `mapPoints` + AvoidsPoint/PreservesSet | `polyEvalP1 q ∞ = ∞` (via `Option.map`); ∞ ∈ `specialSet`; β may be ∞? (paper: β finite; `Option ℚ` includes ∞ for generality) | document that CV only concerns finite points; ∞ handled in target set; if β = ∞ then AvoidsPoint requires q(∞)=∞ ∉ specialSet (false for any q) — restrict β finite in use |
| Möbius/CV typing | `Mzk1MoebiusP1Actual` CV currently `Set (P1Point ℚ)`; `moebiusCriticalValues = ∅` (S3253) | restated target CV is C-point (`Set (P1Point ℂ)` / `criticalValuesOverC`) | **OPEN (S3253 flag (i)/(ii)): need C-variant of Möbius CV type + C-point CV-in-image lemma (stage4); Q-only chart flag (iii)** |
| S/β domain | old shape used `P1Point K` for arbitrary K (Qbar/ℂ) | restated target uses `Finset (P1Point ℚ)`, `β : P1Point ℚ` (rational base), then C-point CV separate | transfer between ℚ-points and ℂ-points via `ofFinite`/coercion; state explicitly that S,β are rational |

**Known bridges still to be supplied (not currently proved as a clean file):**
1. `criticalValuesOverC` vs `Polynomial.criticalValues ℚ` (base change ℚ→ℂ; finite values).
2. Embedding CV values `Set ℂ` into `Set (P1Point ℂ)` (finite points; ∞ excluded).
3. C-point derivative unramifiedness ⟺ CV ⊆ {0,1} + derivative nonzero off {0,1}
   (need per-point local behavior; the restated target includes both clauses, so the bridge is
   mainly for relating to `UnramifiedOver`).
4. Composition law with `polyEvalP1` images (relate `r '' CV(q)` to `polyEvalP1` action).
5. Rational base -> ℂ base lift (hull rational base provider re-target).

---

## 4. ACTION CHECKLIST (per file)

1. **Do not cite** `Mzk1Lemma24Goal`/`StepProviderStatement`/`BaseProviderStatement`/`Lemma24Shape`/
   `Mzk1Lemma24StatementShape` as paper obligation or closure; cite only under "historical/
   progress" labels.
2. **Restated target** = `RestatedLemma24InterfaceActual` definitions (C-point). Any new
   provider file must state its conclusion with `Mzk1Lemma24Target`/`CVInvariant`, not the old
   shape.
3. **Update consumers** `Mzk1Thm25WiringActual:112` (`lemma24` field), `Hull11H6Mzk1UpgradeActual:67`,
   `Mzk1Thm25ConsumerActual:57`, `Mzk1Thm25UnconditionalActual:55`, `Mzk1Thm25P1CompositeConsumerDesignActual`
   to the restated target; keep H6 PARTIAL and wiring status HOLD.
4. **Reuse, do not re-prove:** S1a/S1b/S2/S3/S2-i; F/G/D/M; L2.3 numeric normalization +
   NormalizationTransfer (pattern); rational base; 2.2 CV helpers (`criticalValues_comp_subset`);
   canonical Belyi facts (`belyi_criticalValues_subset` etc.); ported TauCeti Belyi/CriticalValues.
5. **Mark pointer/stub files** S: `Mzk1Lemma24NormalizationDischargeActual`,
   `Mzk1Lemma24NormalizationIntegrationActual`, `Mzk1Lemma24CorrectedTargetActual`,
   `Mzk1Lemma24BaseCaseComplexActual` — not evidence.
6. **Gate table**: frozen; no republish/FINAL ROWS until the restated target + real consumer are
   integrated and mainline/Lead supply final rows. This document changes no Lean file.

---

## 5. CONSUMER TRACKER + BUGFIX STATUS (A282 sync)

From `coord/OLD-TARGET-CONSUMERS-ANALYSIS.md` (mainline A282); lattice maintains the status column.

| deprecated symbol | consumers | needed change | status |
|---|---|---|---|
| `Mzk1Lemma24Goal` (AssemblyActual:20) | AssemblyActual; NormalizationTransferVariant; StepProvider2/3 mentions; audits S3232/S3243/S3244/S3178 | retire Goal; use restated 2.4 target | **PENDING** (files historical until restated) |
| `StepProviderStatement`/`BaseProviderStatement` (AssemblyActual:60/67) | AssemblyActual; StepProvider2/3 notes; S3232/S3236 | restated provider statements; base `s3135_base_provider_complex` re-verify against restated | **PENDING** |
| `Lemma24Shape` (Thm25WiringActual) | Thm25Wiring (h24 field/record); Hull11; probes; ShapeStep/StatementShape; old gate tables | restate over new target; Thm25 wiring must consume restated h22/h24 + real consumer (2.4 o 2.3 o 2.2, 2.3 Moebius) | **PENDING** (stepxi wiring fix) |
| `mzk1Lemma22_partial_induction` (InductionActual:61) | InductionActual; Thm25Wiring; GChoiceDataOfHypotheses; FullGateActual; audits | rewrite induction interface (phi=gPoly + H-on-image + explicit C-point target) | **PENDING bugfix #2** |
| `Mzk1Lemma22CompositionActual.comp` (ratFunc PRODUCT bug) | 14 importers (GChoiceDataOfHypotheses, FullGateActual, GChoiceDataActual, InductionActual, StatementShapeActual, StepConstructionActual, PolyChainRule, PolyMap, PolyUnramifiedComposition, RationalDescent, GChoiceUnramifiedCanonical, StepProvider/NormalizationTransfer chain, audits/probes) | `comp.ratFunc := psi.ratFunc.comp phi.ratFunc` true composition; RECOMPILE/RECHECK ALL 14 importers | **DONE (A282: fixed on disk, checker CITABLE 8 decls); importers recheck outstanding** |
| `Mzk1Lemma22PartialShape` | InductionActual; StatementShapeActual; Thm25Wiring; EtTh09Status; old gate tables | restated target replaces PartialShape in consumer positions; legacy historical only | **PENDING** (Mzk1Lemma24InductionActual NEW green 2246B/3; `Mzk1Lemma22InductionActual` signature still OLD — bugfix #2 pending) |
| Thm25 wiring store-only (`Thm25WiringActual:129`) | Thm25Wiring record | conclusion must use restated h22/h24 + real consumer; no store-only | **PENDING** (stepxi) |
| CV/C-point helpers | bridge table §3 | paper-strength Lemma 2.1(b), restated targets, CV composition | **PENDING** (hull; Mathlib `criticalValues_comp_subset` available) |
| `RestatedLemma24InterfaceActual` (abc) | 2.4 consumers | use as reference target | **FRESH GREEN (A286: mainline verified EXIT0 5255B, CITABLE 9 decls): `Mzk1Lemma24Target` (C-point/specialSet/unramified), `CVInvariant`, `CVCompositionLawStatement`, `SpecialSetPreservationStatement` — FIRST RESTATED TARGET LANDED; audit pending; GATE still NOT PASSED** |
| `S3247CorrectedTargetChecklistActual` (shehdd) | checklist | track | **audit S3248: (a) C-points PASS, (b) no targetSet/unramifiedAt loophole PASS (fixed specialSet), (c) degenerate-witness check PASS (identity/ratFunc=0 fail), (d) vocabulary harmonization with stage4 Mzk1Lemma22Target PENDING; statements NOT proved (interface only)** |
| `Mzk1Lemma22StepInterfaceQActual` (S3249) + `Mzk1Lemma22StepInterfaceQProofActual` (S3252) | new 2.2 induction step interface (explicit Q-membership) + proof of its named TODO | replace old lossy interface; **`step_interface_of_hypotheses_proof` PROVED (S3252)** | **CITABLE: interface 4 decls 2698B C74EE6FF; proof 1 decl 3831B B480D0F5 (probe _S3252StepQProofProbe probe_ok TRUE zero sorry): phi=gPoly D; targetS=S.image(polyMapPoints gPoly); H-on-image via hyp_preservation_full (S3238); card decrease card_image_gPoly_lt; rational-point unramified gChoice_unramified. CONSUMERS use StepInterfaceQ + this proof; OLD `Mzk1Lemma22InductionActual` signature still legacy/deprecated** |
| `Mzk1Lemma22FullShapeHelpersActual` (S3249) | CV composition + base helpers | bridge §3 composition law; CritIn01 over ℂ | **CITABLE 9 decls 3403B DD987A8A probe_ok: `critValues_comp_subset` + `critValues_comp_subset_union` PROVED (CV(r∘q) ⊆ image(CV q) ∪ CV r); BaseGoodData/baseGoodPoly (c*X) + degree/derivative PROVED; 7-row ledger; no True/toy** |
| `RestatedLemma24CVLawActual` (S3255) | restated CV law for corrected target | discharge CV-accounting hypotheses of `s3135_CVInvariant_comp`; bridge §3 composition | **CITABLE 5 decls 3918B 9EE41ECD probe_ok TRUE zero sorry: `criticalValuesOverC_eq` (C-point CV = ported TauCeti `q.criticalValues ℂ`); **`CVCompositionLawStatement` PROVED** (CV(r.comp q) ⊆ (aeval · r)''CV q ∪ CV r, from `critValues_comp_subset` via hull FullShapeHelpers re-export); **`SpecialSetPreservationStatement` PROVED**; `CVCompat` PROVED. CV-accounting hypotheses of `s3135_CVInvariant_comp` DISCHARGED — induction CV step unconditional on CV law** |
| `Mzk1MoebiusP1Actual` (S3253) | Möbius P^1 change-of-chart library for realistic substitution composition | 2.3 Moebius factor in consumer chain (2.4 ∘ 2.3 ∘ 2.2) | **CITABLE 12 decls 7832B 4D63BB55 probe_ok TRUE zero sorry: MoebiusData.comp matrix comp with det(comp)=det(M)det(N)≠0; mapPoints_nonconstant from det≠0 (c=0 / c≠0 case split; pole −d/c ↦ ∞, ∞ ↦ a/c conventions verified); mapPoints_comp_of_finite; derivativeNumerator=ad−bc≠0 ⇒ moebiusCriticalValues=∅; specialSetQ {∞,0,1} mapsTo + moebiusInversion permutes specialSet. FLAGS: (i) CV typed Set (P1Point ℚ) — needs C-variant for restated C-point target; (ii) C-point CV-in-image STILL OPEN (stage4); (iii) Q-only chart. **A305 LAYERING (S3254 duplicate flag corrected): design = Q-typed source; qpilot extension separate; C-file is a DISTINCT C-typed variant (no cycle/dup deletion; future optional `Mzk1MoebiusBasicActual` split). Design re-verified WITH probe: EXIT0 8715, CITABLE 12 decls, src 90123C46 / olean AC95FFC6** | |

**A284 update:** `Mzk1Thm25P1CompositeConsumerDesignActual` CITABLE 10 decls (stepxi) = conditionAL real-consumer design, **NOT closure**; `h22` binding remains history-only; `hullInterfaceNeeds` (6 items) relayed to hull. Gate NOT PASSED.

## 5a. SCOPE DECISION (Lead A313, S3258) — CORRECTED-TARGET STATUS

**COVERAGE STATEMENT (verbatim, to use in all coverage/scope notes): "F=Q component delivered + full-Qbar reduction named (not complete)".**

- **DELIVERED scope = paper 2.4 F=Q component only**: base m(S)=0 + rational Belyi existence, supported by S3236 rational base provider; S3229/S3230 L2.3 normalization existence+transfer; S3223 (G)(F)(D)(M) interface evidence; S3237 separation PROVED; S3255 CV law PROVED; S3232 assembly skeleton.
- **FULL Qbar REDUCTION = NAMED / NOT COMPLETE**: (D) finite-Galois PROVED (S3223 evidence) + infinite fixed field class-B + 2.3 Moebius over Qbar/C + algebraic nested induction class-B = NEW named input **`AlgebraicNestedInductionInput`** (paper 179-206).
- **NO closure claims; GATE NOT PASSED; binding HOLD; FINAL ROWS suspended.**
- Also citable this cycle: **S3256** (C-typed `Mzk1MoebiusP1C` CITABLE 14 decls 6995B probe_ok closes A297 C-flag; layering: design 9329B 18E57C92 unique Q-typed source, qpilot extends, C-file distinct; hull `CVLawProof` 3217B redundant duplicate counted once vs S3255); **S3257** (CritValue minimal staging: `aeval_cast_eval` PROVED; **`CritValueInImageStatement` = NAMED item (i)** with 5-row TODO ledger, no fake theorem; awaits hull `BelyiCvBridge` 4952B; corrected base provider OPEN/class-B candidate per A306).

**HOLD mechanism (A294, S3252):** `tmp/xif_hold_files.txt` is read by `tools/xif_guarded_queue.ps1` (filter at line 8) — HOLD entries: `Mzk1Thm25Unconditional` (+probe), `Mzk1Lemma22FullGateActual` (old invalid path), `Mzk1Lemma24BaseCaseComplex` (deprecated). Binding is **NOT auto-queued**; un-HOLD only by explicit Lead decision after a real consumer + restated full gate exist. Verified hold file contents match. GATE NOT PASSED; binding HOLD; FINAL ROWS suspended.

**RULE:** any import/use of symbols in §1.1-1.2 must be re-pointed to restated interfaces or explicitly marked historical; no gate/closure claim under old target.

---

## 6. References

- External review / correction: mainline **A277**, abc A277 ack, lattice **AUDIT_LEDGER 20:40**.
- **A282 consumer analysis:** `coord/OLD-TARGET-CONSUMERS-ANALYSIS.md` (mainline; 14/22/12/7 counts); comp bugfix #1 DONE (CITABLE 8 decls); InductionActual interface bugfix #2 pending.
- Assignment + conditional sign-off: mainline **A279/A280/A281**, `S3246AssignmentsRecordActual`.
- Integrity record: `S3244IntegrityCorrectionActual` (five defects verbatim).
- Restated reference implementation: `RestatedLemma24InterfaceActual.lean` (+ probe).
- Vocabulary: `S3246` ("P1Point Q + CV Set (P1Point C); specialSet={0,1,inf}").
- Pins: registry 14041 / gate in flux / record 18800; L8 frozen; no registry edits.

*Generated by lattice under gate freeze; fact-only cross-reference, no Lean edits, no gate writes.*
