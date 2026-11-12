# FOUNDATIONS-IUTIV — IUT IV §1 / Theorem 3.11 → Corollary 3.12: real objects vs conditional interfaces vs paper gaps

Status: inventory only (Lead A409/A411/A426/A429). **No wiring work, no closure claims.**
Canonical gate pin: FINAL PIN V150@18248/CFC6CE08; GATE NOT PASSED; binding HOLD; L8 FROZEN; registry 14041 / record 18800.
Generated 2026-11-11 for stepxi (史蒂). Registry frozen 14041; gate NOT PASSED; h22 binding HOLD.

Source of truth for this scan: read-only survey of `LeanFormal/IUT/**`, `coord/**`,
`tmp/sheaf/xif/paper/**`, and the corpus `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt`.
Cross-references (existing notes, do not duplicate): `coord/IUTIV-SECTION1-PLAN.md`,
`coord/IUT-EXTERNAL-OBJECTS-INVENTORY.md` §L8, `coord/OPEN-HARD-PROBLEMS.md`,
`coord/CURRENT-HARD-POINTS.md`, `coord/ENDGAME-DEPENDENCY-LEDGER.md`.

Legend:
- **REAL**: concrete definition/object + proved theorem, no unproved field in the result.
- **MODEL**: concrete object, but explicitly a *calibration* / stand-in, not the paper's object.
- **IFACE**: structure whose fields are data and/or named propositions; conditional only.
- **NAMED**: paper input recorded as an explicit unproved field (class-B).
- **GAP**: no formal object yet (paper text only).

---

## 1. REAL objects (concrete, proved)

### 1.1 IUT IV §1 arithmetic/log-volume prerequisites
| Object | Location | Status |
|---|---|---|
| R-arithmetic divisors `IUTIVArithmeticDivisor`, `deg`, `ndeg`, `part`, `eDegree`, fiber contributions, pullback | `LeanFormal/IUT/IUTIV/Estimates/ArithmeticDivisorDegree.lean:79,113,216`; pullback invariance `:304,325` | **REAL** (Def 1.9 core; 104 theorems) |
| Height-box layer (`absValAt`, support, h_non/h_arc/h^tor) | same file `:1046,1054` | **REAL** (Lemma 1.3 items, defined locally) |
| p-adic different tower: normalized different inequality; tame equality | `DifferentTowerEstimate.lean`, `DifferentTameEquality.lean`, `DifferentDegreeUpperBound.lean` | **REAL** (Prop 1.3(i) complete per Section1 notes; (ii) still gap) |
| Archimedean tensor metric: ℂ⊗_ℝℂ ≅ ℂ×ℂ, inner products/norms, primitive unit algebra maps | `ArchimedeanTensorMetric.lean` (13 thms), `ArchimedeanMultiTensorMetric.lean` (32 thms) | **REAL** partial Prop 1.5 (i)/(ii)-type facts; general (iii)/(iv) gap |
| Explicit θ/PNT estimates: θ two-sided (2/3)x ≤ θ(x) ≤ (4/3)x eventually; `π(η) ≤ 4η/(3logη)`; sixfold binomial window | `Section2.lean:393,409` and helpers | **REAL** (Prop 1.6, Prop 2.1(ii) two-sided; explicit numeric PNT constants still gap) |
| Prop 1.7 weighted-average identities | `Section1.lean` `iutIVProp17*:199` | **REAL** |
| Theorem 1.10 step-(v) real-number algebra: collection bound, sum/average, final inequality; divisor average; distinguished-slot symmetrization | `StepVProcessionAverage.lean:35,54,68`; `StepVDivisorAverage.lean`; `StepVDistinguishedSlotAverage.lean` | **REAL** (real-number layer only; arithmetic inputs free) |
| Concrete p-adic arithmetic tuples: q_n norms, local different, log-shell lattices, normalized log-volume ≤ paper bound | `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVAssembly.lean:602`, `FinitePlaceStepVRealBound/Lambda/JInvariant.lean`; `FinitePlaceLogShellScalingAssembly.lean` | **REAL** (in stated tuple scope) |
| Product-local-field hulls: unit region, λ-regions, compactness, least region, hull=∩λO, normalized log-volume monotonicity/bounds | `HolomorphicHull/LocalFieldProductHull.lean:37,40,100,119,137,203,251,269,331,347` | **REAL** (Remark 3.9.5 analytic prerequisite; caveat in header: IQ identification separate) |

### 1.2 IUT III §3.12 arithmetic q-pilot layer (real arithmetic, not paper identification)
| Object | Location | Status |
|---|---|---|
| `FinitePlaceQCandidate` (actual completion q, q≠0, norm<1, valuation/order data), nonempty | `Foundations/NumberField/LocalQParameter.lean:39,111` | **REAL** |
| local signed q-log / magnitude: `localSignedLog`, `localLogMagnitude`, norm/valuation identities | `Corollary312/ArithmeticQPilotLogVolume.lean:35,39` | **REAL** arithmetic identities |
| base change: `residueNormBase`, ramification/residue degree, completion norm degree, qNorm = base^exponent, order normalization | `ArithmeticQPilotBaseChange.lean:32,113,118` | **REAL** |
| global fibers: `UpperPlaceFiber`, all selected upper places, exact fiber indexing, `sum_completionNormDegree_eq_fieldDegree` | `ArithmeticQPilotGlobalNormalization.lean:40,189` | **REAL** |
| finite theta packet → positive packet transport (det/log-volume/rescale) | `StepXI/ThetaPacketBridge.lean:25` | **REAL** transport (not paper Hodge theater) |

These files say explicitly: no Tate uniformization, no construction of paper global q-pilot weights, no identification with paper's actual q-pilot/theta-hull. Treat as **REAL arithmetic sub-layer**, not Cor 3.12.

### 1.3 IUT III Theorem 3.11 source layer (abstract data + real construction laws)
- `LeanFormal/IUT/IUTIII/Theorem311/` (100 files): `OriginalInput` (`SourceOriginalInput.lean:41`) has fields `initial : SourceDefinition31Data`, `family : SourceHodgeTheaterFamily`, `index_equiv`, `arithmetic_alignment`; `MultiradialOutputKernel.Core` (`:12`) is a 19-field algebraic Ind1/2/3 kernel. These are **REAL data structures with proved laws**, but the underlying `SourceDefinition31Data`/`SourceHodgeTheaterFamily` are abstract models, **not** the paper's Hodge theaters/Frobenioids/Kummer maps/prime strips.
- Constructive column realizations: `SourceColumnCarrierIdentification.coreColumnRealization:136`, `inputColumnRealization:251` — **REAL** constructions with Ind1/2/3 laws over an arbitrary source input.
- Certificate hull wiring at the concrete model: `CertificateHullWiringRealization.iqCarrierModelWiringCertificate:106` — **MODEL** (model values q=-1, theta=0).
- `StepXI/ParametricStepXI.StepXIInput:27`: fields q/theta/target + ipl/she/apt evidence; `StepXIInput.toContract` assembles a `StepXIContract` **only when the fields are supplied** (conditional; see §2.4).

---

## 2. Conditional interfaces (all unproved paper content explicit)

### 2.1 `IQHullLogVolumeInterface` (IUT III Cor 3.12 hull/finiteness interface)
`SourceHullCompactnessReduction.lean:52` — fields: `imageSet`, `hull`, `imageSet_subset_hull`, `logVolume : Set X → ENNReal`, `logVolume_mono`, `unitRegion`, `scaleShift`, `hull_subset_scaleShift`, `unitRegion_logVolume_lt_top`, `scaleShift_unitRegion_logVolume_le`.
Proved from the fields: `imageSet_logVolume_le_hull` and `hull_logVolume_lt_top:95` (**conditional finiteness**; this is the Cor 3.12 finiteness half).
**IFACE**: the intended carrier is the paper's inductive system `IQ(S±_{j+1}; n,◦D^vdash_{vQ})`, which is NOT formalized. `singletonRealWitness:112` is only a satisfiability/consistency check, explicitly "not a model of the paper's carrier".

### 2.2 Source-side hull data and its unsatisfiability warning
- `SourceUnitRegionHaarData` (`HolomorphicHull/IQCarrierHaarData.lean:159`): fields unitRegion/scaling/degreeBound + hull ⊆ scaled region + degree bounds — **IFACE**; `sourceUnitRegionHaarInterface:181` converts it to a hull interface (conditional).
- `ValueHullCompactnessInput` (`SourceHullInterfaceDischarge.lean:205`): **IFACE**. Under pointwise degree faithfulness, its value-monoid hull is unbounded: `sourceHullVolume_not_lt_top_of_degreeFaithful:170`, `not_nonempty_valueHullCompactnessInput_of_degreeFaithful:232`. **Consequence**: naive "hull = value-monoid closure" cannot be used; the paper's ring-of-integers/O-module structure is required (this is exactly the missing carrier structure).
- `Cor312SourceHullNormalizationData` (`SourceHullNormalizationConditionalClosure.lean:104`): conditional normalization data; `cor312HullNormalizationConditionalClosure:354` is status **interface** ("conditional closure", not proved).

### 2.3 Concrete carrier model (calibration only)
`IQCarrierConcreteModel.lean:193` `iqCarrierModelInterface : IQHullLogVolumeInterface Real` with `hull = Set.Iic 0`, normalized volumes 0. Model targets listed in its header; **MODEL**, not paper carrier. Its epsilon comparison constructors are conditional on named inputs:
`iqCarrierModel_epsilonComparison:413` requires `hval` (uniform valuation bound) and `iqCarrierModel_epsilonComparisonAdditive:431` requires `hadd` (ABC height–weight additive bound). No ABC is derived.

### 2.4 IUT III 3.11 → 3.12 contract
`StepXI/Contract.lean:32` `StepXIContract`: qSigned/thetaSigned/targetSigned reals + proofs q<0, q≤target≤theta + `ipl`/`she`/`apt` Prop fields with evidence fields. `Cor312Conclusion` (`:46`) is only the ordered inequality; `cor312Conclusion_of_contract:49` is a one-line transitivity proof. `stepXIContractConstruction:61` is status **pending**: construction from IUT source data (Ind1/2/3, IPL/SHE/APT, holomorphic-hull/determinant/log-volume) is unfinished.
The file states explicitly: these structures are *contracts for obligations*, not definitions of the paper's Hodge theaters, Frobenioids, prime strips or Kummer maps.

### 2.5 Cor 3.12 → ABC comparison interface (two named IUT IV gaps)
`LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean`:
- `Cor312EpsilonArithmeticComparison` (`:224`): data `logShellPoint` plus **two named gaps**:
  1. `height_le_normalizedRegionVolume` — IUT IV §2 height vs normalized region log-volume comparison;
  2. `regionVolume_le_normalizedWeight` — IUT IV §2 main log-volume computation (θ-pilot bound + residual).
- `Cor312ToABCBridgeInterface` (`:404`): carrier + `hullData : IQHullLogVolumeInterface carrier` + per-ε comparison.
- `cor312ToABCBridge_abcConjecture:446` is **proved conditionally** on an inhabitant; `cor312ToABCBridgeInterface_nonempty_iff_abcConjecture:605` calibrates strength (Nonempty ↔ ABC), so the interface is exactly as strong as ABC and proves none of its gaps.
- **IFACE/GAP**: both named gaps are IUT IV §2 paper links; no proof exists in repo.

### 2.6 Problem E / H6 named deep inputs (separate layer, not bridge inputs)
- `Mzk1HullEInputsActual.HullEH5NamedInputs:56`: `oInverseNormalization`, `hull_le_image_volume` (class-B); `HullEH7NamedInput:65`: `arbitraryIterateIndependence` (class-B, deep Ob9). Conditional assembly `hullE_genEll_intermediate:101`, Cor 3.12 hull+det projection `hullE_cor312:113`. Status: conditional, explicit named parameters.
- `AbsTopIII05RefinedActual.s3171RouteSlot_display_and_abc:133`, `absTopIII05Refined_with_s3171RouteSlot:142`: conditional route-slot assets (named inputs explicit).
- EtTh realization: `Mzk1EtThRealizationConsumerActual` CITABLE 14/11293 (3 class-B named: geometric realization, Frobenioid representation, actual theta transform; 8 A-class reuse rows; conditional consumers).
- GenEll 2.1 consumer: `GenEll21GeometricCoreConsumerActual` currently RED (not citable); do not cite.
- 2.4/2.2 rational F=Q layer is green (fold base unconditional finite-β; `Mzk1Consumer24AdapterUnconditionalActual`), but the paper-scope Q̄ reduction remains **NAMED** (`AlgebraicNestedInductionInput`, Problem C).

---

## 3. Gaps against the paper (IUT IV §1 and 3.11 → 3.12)

### 3.1 IUT IV §1 (`IUT IV.txt` L391–2328; Section1 notes)
Already-real: Prop 1.3(i), Prop 1.6, Prop 1.7, Def 1.9 core, Archimedean tensor facts (partial), Theorem 1.10 step-(v) real-number algebra, height-box.
Still GAP (no machine object; Section1 cards 1–5,8,10):
1. **Prop 1.1** p-adic tensor ring `R^{pM}` normalized containment (tensor/different powers) — missing; consumer of Prop 1.4.
2. **Prop 1.2** differents/log_p estimates — missing (depends 1).
3. **Prop 1.4** nonarchimedean normalized log-volume estimate — missing; needs a log-volume/Hodge-theater layer (paper log_p).
4. **Prop 1.5** full archimedean metric estimates (general |I|, λ^{|I|}B_I) — partially real (tensor metric file), general statement missing.
5. **Prop 1.8** elliptic torsion/Serre open image layer — missing (large).
6. **Theorem 1.10** actual θ-pilot log-volume estimate: display/statement layer exists conditionally (`S3171IUTIVSection1DisplayActual`, inputs `hCor312` + paper Step-(v) slack), but the log-volume objects and the estimate are not proved; needs the missing local log-volume layer + Cor 3.12 constant C_Θ.
7. **Explicit estimates Prop 2.2** (numerical PNT constants: ηprm=5·10^20, ξprm=10^15, π bound, θ error 0.00071x) — not formalized (Section2 notes say so explicitly).
8. **IUT IV §1 arithmetic transition / theta-link / log-link objects** — no named Lean objects (`ArithmeticTransition*` = 0 hits); only abstract Theorem-3.11 data/procession-isomorphism interfaces (`SourceAdjacentColumnProcessionIsomorphism`).

### 3.2 Theorem 3.11 → Corollary 3.12 (III)
- The Step-(xi) proof boundary is only a **contract** (`StepXIContract`); its construction is pending (`stepXIContractConstruction`).
- Realizations exist for individual pieces (column realizations, theta packet transport, certificate wiring at the model, hull determinant/log-volume pieces), but there is no literal formalization of the paper's Hodge theaters, Frobenioids, Kummer maps, theta-links, prime strips.
- Ind1/2/3 exist as abstract kernel laws (`Core`); the general Indeterminacy bounds (paper Step (iv)) are modeled only in finite instances (`Indet01-03*`), and the full Ind layer is flagged as a gap.
- Cor 3.12 hull/finiteness: finiteness is PROVED from `IQHullLogVolumeInterface` fields, but the carrier identification `IQ(S±_{j+1}; n,◦D^vdash_{vQ})` is not formalized; naive value-monoid hull is provably unbounded under degree faithfulness (see §2.2), so the carrier structure is essential (not cosmetic).
- Cor 3.12 → ABC: two IUT IV §2 comparisons are named gaps; interface strength calibrates to ABC, so no closure is hidden.

### 3.3 Problem E named deep inputs (out of current scope)
H5 O^x stabilization (class-A proved) + two H5 class-B named; H7/Ob9 arbitrary iterate (class-B); AbsTopIII05 deep reconstruction (class-B); EtTh three class-B named; GenEll 2.1 consumer RED; Problem D precise witness existence + line-bundle iso named; Problem C Q̄ m/d induction named; Problem B Lemma 2.3 Q̄ Möbius separation not formalized (rational Möbius assets only).

---

## 4. Recommended foundational work (no wiring, dependency order)

1. **Local p-adic tensor/log-volume layer**: formalize `R^{pM}` normalized subring via different powers (Prop 1.1), then Prop 1.2/1.3(ii), then Prop 1.4's normalized log-volume on local fields; connect to existing `ArithmeticDivisorDegree` deg/ndeg and `FinitePlaceStepV*` p-adic tuples.
2. **Literal carrier object** `IQ(S±_{j+1}; n,◦D^vdash_{vQ})`: model the inductive system/limit with ring-of-integers/O-module structure; either instantiate `IQHullLogVolumeInterface` from it or prove the obstruction; do not use `iqCarrierModelInterface`/singleton witness as the paper carrier.
3. **StepXIContract construction**: Ind1/2/3 from source procession data, IPL/SHE/APT from paper, hull determinant/log-volume normalization; keep the contract-vs-definition distinction.
4. **Cor 3.12 comparison gaps**: height comparison and region log-volume computation (IUT IV §2); explicitly named in `Cor312EpsilonArithmeticComparison`.
5. **Theorem 1.10 log-volume estimate**: build the log-volume object of the theta-pilot from (1)+(2); prove the display; keep `hSlack` and `hCor312` as explicit inputs until foundation (1) lands.
6. **Index/height layer**: arithmetic height functions and explicit PNT constants (Prop 2.2) for §2.
7. **Problem B/C layer** (Q̄/2.3): formalize Lemma 2.3 Möbius separation over Q̄ and the algebraic nested (m,d) induction before using any Q̄-scope consumer.

Cautions:
- Do not derive ABC from the mere existence of an interface; only the conditional theorem `cor312ToABCBridge_abcConjecture` is proved.
- Do not treat `singletonRealWitness` / `iqCarrierModelInterface` / model certificates as paper carriers.
- Do not cite RED files (e.g. `GenEll21GeometricCoreConsumerActual`).
- The parked goal-level consumer `Mzk1Cor312ToABCConsumerActual` (Lead A409) is not part of this foundation inventory and is not claimed as closure.

---

## 5. Quick file map

- IUT IV estimates: `LeanFormal/IUT/IUTIV/Estimates/` (14 files; real arithmetic estimates + two pending obligations).
- IUT III Cor 3.12: `LeanFormal/IUT/IUTIII/Corollary312/` (ArithmeticQPilot*, Comparison, Routes, Obligations, StepXI/*, StepXI/HolomorphicHull/*).
- Theorem 3.11 source: `LeanFormal/IUT/IUTIII/Theorem311/` (100 files, abstract data + constructions).
- Bridge/interface: `LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean`.
- Notes: `coord/IUTIV-SECTION1-PLAN.md`, `coord/IUT-EXTERNAL-OBJECTS-INVENTORY.md` §L8, `coord/OPEN-HARD-PROBLEMS.md`, `coord/CURRENT-HARD-POINTS.md`, `coord/ENDGAME-DEPENDENCY-LEDGER.md`.
- Conditional E/H6 assets: `tmp/sheaf/xif/paper/Mzk1HullEInputsActual.lean`, `AbsTopIII05RefinedActual.lean`, `Mzk1EtThRealizationConsumerActual.lean`, `Mzk1GeometricCorePreciseActual.lean`, `Mzk1P1ConsumerDeepInputsActual.lean`.


---

## 6. REAL-object closure table (file:line + declarations + citable evidence)

Citable evidence method: core LeanFormal modules have fresh oleans under .lake/build/lib/lean (per-module checked); representative declarations verified by tmp/sheaf/xif/paper/_FOUNDATIONS-IUTIV-CitableProbe.lean (EXIT=0, results:210254): deg_pullback, ndeg_pullback, iutIVProp17, iutIVProp21ii_theta_two_sided_eventually, processionAverage_le, stepVPaperLogVolumeBound, measure_hull_lt_top, hull_logVolume_lt_top, sum_completionNormDegree_eq_fieldDegree, cor312ToABCBridge_abcConjecture — all axioms exactly [propext, Classical.choice, Quot.sound]. A declaration is called citable below when its module has a fresh olean and either appears in that probe or is structurally imported from the same module.

### 6.1 IUT IV arithmetic/analytic REAL objects

| # | objects (file:line) | declarations (proved) | citable | reuse classification |
|---|---|---|---|---|
| R1 | ArithmeticDivisorDegree :79,113,216,304,325,1046 | weight, deg/ndeg, pullback, deg_pullback, ndeg_pullback, HeightBoxLayer (absValAt, hweightvol, hpoint) | fresh olean + probe | REUSE-AS-IS (Def 1.9 / height box) |
| R2 | ArchimedeanTensorMetric :1-200 | complexTensorToProd_*, complexTensor_algEquiv_inner, complexTensor_continuousRingEquiv_inner | fresh olean | REUSE, then EXTEND to general |I| / lambda^|I| B_I (Prop 1.5(iii)(iv)) |
| R3 | ArchimedeanMultiTensorMetric :1-250 | tensorMetric_tprod, conjTwist_apply, characterIndex, twistPattern | fresh olean | REUSE (multi-factor tensor metric) |
| R4 | DifferentTowerEstimate :1-120 | count_differentIdeal_tower, iutIVProp13i_normalizedDifferent_ge | fresh olean + probe | REUSE-AS-IS (Prop 1.3(i) inequality) |
| R5 | DifferentTameEquality :1-150 | count_differentIdeal_eq_of_tame, iutIVProp13i_normalizedDifferent_eq_of_tame | fresh olean | REUSE-AS-IS (Prop 1.3(i) equality) |
| R6 | DifferentDegreeUpperBound :1-200 | not_map_dvd_differentIdeal_of_degree_not_mem, dvr_ideal_eq_pow_factorCount, dvr_factorCount_lt_of_not_dvd | fresh olean | REUSE partial; EXTEND with Prop 1.3(ii) upper bound |
| R7 | ElementaryEstimates :76,88,101,121 | iutIVThm110_e1..e4 (+e5/e6) | fresh olean | REUSE-AS-IS (Thm 1.10 finite bookkeeping) |
| R8 | Section1 :199 | iutIVProp17 + lemmas | fresh olean + probe | REUSE-AS-IS (Prop 1.7) |
| R9 | Section2 :393,409 | iutIVProp21i_log_le_self, iutIVProp21ii_theta_two_sided_eventually, iutIVProp16_* | fresh olean + probe | REUSE-AS-IS (Prop 1.6, 2.1 two-sided) |
| R10 | StepVProcessionAverage :35,39,54,68 | collectionBound, sum_collectionBound, processionAverage_eq, processionAverage_le | fresh olean + probe | REUSE-AS-IS (Thm 1.10 step (v) real algebra) |
| R11 | StepVDivisorAverage :33,46 | weight_finite_eq_inertiaDeg_mul_log, eDegreeUnnormalized_eq_weightedAverage | fresh olean | REUSE-AS-IS |
| R12 | StepVDistinguishedSlotAverage :1-120 | weightedSum_*_independent, weightedAverage_*, processionNormalized_le_of_distinguishedBounds | fresh olean | REUSE-AS-IS |
| R13 | p-adic tuples: ABCBridge/Geometry/FinitePlaceStepVAssembly:602, FinitePlaceStepVRealBound:25,61, FinitePlaceStepVLambda/JInvariant, FinitePlaceLogShellScalingAssembly | arithmeticTuple_stepV_normalizedLogVolume_le_paperBound, stepVPaperCorrectionSum_le, stepVPaperLogVolumeBound, stepVLambda*, arithmeticTensorIntegerLogShellScalingAssembly* | fresh oleans | REUSE; EXTEND by assembling into Thm 1.10 statement (object/constant layer) |
| R14 | LocalFieldProductHull :37,40,100,119,137,203,251,269,331,347 | unitRegion/region, isCompact_*, measure_*_lt_top, hull* theorems, normalizedLogVolume_* | fresh olean + probe | REUSE, then EXTEND-IDENTIFICATION with the IQ carrier (M1/M2 warning) |

### 6.2 IUT III 3.12 REAL arithmetic sub-layer

| # | objects (file:line) | declarations | citable | reuse classification |
|---|---|---|---|---|
| R15 | Foundations/NumberField/LocalQParameter :39,111 | FinitePlaceQCandidate, finitePlaceQCandidate_nonempty | fresh olean | REUSE-AS-IS (candidate data) |
| R16 | ArithmeticQPilotLogVolume :35,39 | localSignedLog, localLogMagnitude, qNorm_*, selected* | fresh olean | REUSE-AS-IS (local arithmetic) |
| R17 | ArithmeticQPilotBaseChange :32,113,118 | residueNormBase, localRamificationIndex, localResidueDegree, qNorm_eq_residueNormBase_zpow | fresh olean | REUSE-AS-IS |
| R18 | ArithmeticQPilotGlobalNormalization :40,189 | UpperPlaceFiber, AllSelectedUpperPlaces, selectedUpperEquivFiberSigma, sum_completionNormDegree_eq_fieldDegree | fresh olean + probe | REUSE; EXTEND into paper q-pilot/global theta-pilot identification (named, not proved) |
| R19 | StepXI/ThetaPacketBridge :25 | toPositivePacket + det/logVolume/rescale transport | fresh olean | REUSE transport; paper Hodge-theater construction remains GAP |

---

## 7. MODEL / IFACE object table

### 7.1 MODEL (concrete but calibration, never the paper object)

| # | object (file:line) | status | reuse classification |
|---|---|---|---|
| M1 | IQCarrierConcreteModel:193 iqCarrierModelInterface | real-line calibration model (hull = Set.Iic 0, volumes 0) | MODEL only (testing/validation); NOT a substitute for the paper carrier. Its gap constructors :413/:431 are conditional on hval/hadd (ABC-strength inputs) |
| M2 | SourceHullCompactnessReduction:112 singletonRealWitness | satisfiability witness (one point) | MODEL only (consistency check; doc says not paper carrier) |
| M3 | CertificateHullWiringRealization:106 iqCarrierModelWiringCertificate | model certificate (q=-1, theta=0) | MODEL only |
| M4 | Cor312CarrierRealizationSpec (Bridge) | concrete test carriers for bridge arithmetic | MODEL / VALIDATION |
| M5 | FinitePlace* arithmetic tuple models (Geometry) | actual p-adic tuples under abstract label data | REUSE where stated; paper identification named |

### 7.2 IFACE (data/named-Prop structures; conditional only)

| # | object (file:line) | fields/named content | reuse classification |
|---|---|---|---|
| I1 | IQHullLogVolumeInterface (SourceHullCompactnessReduction:52) | imageSet/hull/logVolume/unitRegion/scaleShift + monotonicity and scaling laws; hull_logVolume_lt_top PROVED from fields | IFACE; finiteness half reusable; carrier identification missing |
| I2 | SourceUnitRegionHaarData (IQCarrierHaarData:159) / ValueHullCompactnessInput (SourceHullInterfaceDischarge:205) | unitRegion/scaling/degreeBound + bounds; value-hull compactness data | IFACE + WARNING: degree-faithful value-hull form provably unsatisfiable (:170,:232); needs ring-of-integers/O-module structure |
| I3 | Cor312SourceHullNormalizationData (SourceHullNormalizationConditionalClosure:104) | frozen comparison data / hull bound | IFACE (conditional closure; status interface :354) |
| I4 | StepXIContract (Contract:32) / Cor312Conclusion (:46) | q/theta/target signed reals + monotonicity + ipl/she/apt Props; conclusion = ordered inequality | IFACE (contract, not definitions); construction pending :61 |
| I5 | Cor312EpsilonArithmeticComparison (Cor312ToABCBridgeInterface:224) | logShellPoint + TWO named IUT IV §2 gaps | IFACE / GAP: exactly the two unproved comparisons |
| I6 | Cor312ToABCBridgeInterface (:404) | carrier/hullData/epsilonComparison | IFACE; strength Nonempty<->ABC (:605); conditional theorem :446 |
| I7 | ABCFrontier + Frontier reductions (Bridge) | Frontier clauses; abcConjecture_of_frontier routes | IFACE (frontier clauses named) |
| I8 | HullEH5NamedInputs/HullEH7NamedInput (tmp Mzk1HullEInputsActual:56,65) | class-B H5/H7 named deep inputs; hullE_genEll_intermediate conditional :101 | IFACE (E layer; separate from ABC graph) |
| I9 | AbsTopIII05 route slot, EtTh 3 named, GenEll 2.1 consumer | class-B/deep named | IFACE; GenEll consumer RED (not citable) |

---

## 8. Extension plan (no new mathematics; attach to paper text)

Ordered by dependency; each item states the exact extension of an existing REAL/IFACE object:

1. Prop 1.1 tensor-ring layer (GAP -> new definitions): normalized subring of the p-adic tensor ring via different powers; consumers Prop 1.2/1.4. No repo object exists.
2. Prop 1.2/1.3(ii) different estimates (EXTEND R4/R6): local log-different and the upper bound d_i <= d_0 + n_i + 1/e_0. Reuse DifferentTameEquality/DifferentTowerEstimate.
3. Prop 1.4 local normalized log-volume (GAP -> new object): paper local log-volume/Hodge-theater layer; connect to LocalFieldProductHull.normalizedLogVolume_* (R14) and ArithmeticDivisorDegree degree/weight (R1).
4. Prop 1.5 general archimedean (EXTEND R2/R3): general |I| tensor metric and lambda^|I| B_I containment; reuse tensor metric lemmas.
5. Prop 1.8 elliptic/Serre (GAP): torsion open-image layer; consumers Thm 1.10 / Cor 2.2.
6. Thm 1.10 actual log-volume estimate (EXTEND R7/R10/R13 + R14): assemble the log-volume object and the display; keep hSlack/hCor312 named until (1)-(5) land.
7. Cor 3.12 carrier (EXTEND I1/I2 + M1/M2 -> real object): model the inductive-system carrier IQ(S+-; n, D^vdash) with O-module/ring-of-integers structure; prove either an inhabitant of IQHullLogVolumeInterface from it or the obstruction; do not use the real-line model. Consumers: SourceHullNormalizationConditionalClosure (I3), StepXIContract (I4).
8. The two IUT IV §2 comparison gaps (I5 fields): height comparison (height_le_normalizedRegionVolume) and region log-volume computation (regionVolume_le_normalizedWeight); these directly turn cor312ToABCBridge_abcConjecture into an unconditional theorem. Attach Cor312ComparisonGapReduction/SupplyLayer reduced inputs and the hull/carrier layer.
9. IUT IV §1 -> §2 edge (GAP): no Lean theorem connects the Thm 1.10 display (S3171IUTIVSection1DisplayActual) to the §2 Cor312 comparisons; this paper-level comparison is the missing edge of the last chain.
10. Frontier/elliptic alternatives (I7 + ABCEllipticHeightCriterion): only equivalences; do not route through ABCHeightWeightAdditiveBoundV2 (ABCFrontierHeightWeightRefutation blocks that factorization).

Status vocabulary: REAL/REUSE = proved and directly usable; EXTEND = proved core plus paper-defined missing layer; IFACE/MODEL = conditional/calibration only. No closure claims; gate NOT PASSED; binding HOLD; pins 14041.
