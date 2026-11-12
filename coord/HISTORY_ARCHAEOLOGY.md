# HISTORY ARCHAEOLOGY — ABC/IUT formalization history (tmp/ + coord/ + external)

Date: 2026-11-07. Author: transport (deep-auditor).
Scope: recursive scan of `tmp/` (220 directories, 2779 keyword-bearing files),
`coord/*.md`, and external Lean projects (Takkun, promachina, PriestAmbrose, etc.).

Status legend:

```text
ACTUAL       = compiled module with olean; axioms only propext/Classical.choice/Quot.sound
CONDITIONAL  = actual theorem with explicit input fields; not a source construction
STATEMENT    = Prop/def/structure only; no inhabitant/proof
REFUTED      = actual negative theorem / counterexample
INVALID      = placeholder, sorry, circular field, or wrong target
UNVERIFIED   = external source claims actual but no current olean/recompile here
```

## 0. Executive verdict

1. **No paper-level Cor 3.12 exists in the history.** The best shape is Takkun's
   `PilotVolumeData.cor312` (conditional on `containment`) plus the `thm110`
   elementary deduction. It is a logical skeleton, not a source construction.
2. The strongest **actual** project-side objects are: the IUT IV Step V local
   theta bound (`FinitePlaceStepVLambda`/`StepVAssembly`), the signed arithmetic-
   tuple certificate (`FinitePlaceIQHullSignedCertificateNonvacuous`), the
   weighted q-pilot normalization (`NativeGlobalQPilotNormalizedLogVolumeActual`),
   the S2807 theta-hull identity reductions, and the S2800 conditional ABC bridge.
3. The historically closest **paper-faithful** bridge is C9's
   `XiEToXiFOutputReadoutProjection(C)`: fixed admissible C, q-pilot mark into the
   restricted final-evaluation output family, exact or signed-epsilon. The C9
   `U2K2 -> sQ3` trace shows no source constructor for this attachment.
4. The current S2935/S2936/S2958 route is **not** the historical shortest path;
   S2935 is an ABC-type height bound and S2958/S2953 are tautological/circular
   certificates. Reproducing the paper is better served by the Step V/S2807/C1
   objects listed below.

## 1. Directory scan

- `tmp/`: 220 directories, 2779 files matching the core keyword set.
- Full per-directory `md/lean` count inventory: [HISTORY_ARCHAEOLOGY_DIRS.csv](HISTORY_ARCHAEOLOGY_DIRS.csv).
- Key-file list: `tmp/_history_keyword_files.txt` (2779 paths).
- Large historical hubs: `tmp/sheaf` (947 md / 9820 lean), `tmp/external` (171/24218),
  `tmp/n8-20261018` (47/2258), `tmp/dsh-oct6-openai-math-survey` (132/3542),
  `tmp/TauCeti` (29/20990).

Priority-directory result table (counts are recursive, excluding `.lake`):

| dir | md | lean | result |
|---|---:|---:|---|
| theta-link-resolution-20261020 | 0 | 1 | only MonoidCoreAxioms probe; no source theta-link |
| theta-route-20261017 | 0 | 1 | only check-probe |
| source-theta-pilot-iq-20261018 | 0 | 0 | empty |
| source-theater-construction-20261016 | 0 | 2 | draft + axiom probe, no actual source theater |
| source-facing-frontier-map-20261016 | 6 | 0 | report only; sees Step XI contract as 12 fields |
| signed-cert-20261017 | 0 | 1 | probe of actual signed certificate |
| signed-cert-nonvacuous-20261017 | 0 | 1 | probe of actual floor certificate |
| card-ampl-solidification-20261016 | 0 | 1 | probe of actual Card-AMPL supply |
| certificate-hull-wiring-20261016 | 0 | 1 | probe of actual wiring; no new carrier |
| cor312-carrier-instantiation-20261016 | 0 | 2 | statement probe only |
| cor312-gap-dictionaries-20261016 | 1 | 4 | actual spec file; **jointly refutable** (see failures) |
| cor312-gap-reduction-20261016 | 0 | 6 | actual reductions, conditional on dictionaries |
| cor312-to-abc-cards-20261016 | 0 | 3 | paper cards only; no proof |
| fix_qpilot_global_normalization_20261016 | 0 | 1 | probe of arithmetic q-pilot normalization module |
| hull-determinant-log-volume-20261016 | 1 | 1 | probes only; no construction |
| hull-presentation-routes-20261016 | 6 | 9 | actual hull-envelope layers + negative results |
| iq-carrier-alignment-20261016 | 0 | 1 | probe only |
| native_hull_bound_attempt_20261016 | 0 | 3 | probes only; no hull bound |
| native_iq_carrier_haar_20261016 | 0 | 1 | probe of actual Haar cor312 consumer |
| native_* (22 dirs) | 0-1 | 1-4 | mostly probes; actual modules live in LeanFormal |
| stepxi-contract-reduction-20261016 | 0 | 1 | probe of actual reduction lemmas |
| verify-supply-layer-20261016 | 0 | 13 | copies/probes of actual gap-reduction layer |
| source-torsion-carrier-20261016 | 0 | 3 | probes of source torsion carrier |
| log-shell-carrier-20261016 | 0 | 9 | probes of log-shell carrier |
| multiradial-output-reduction-20261016 | 0 | 1 | probe only |
| ind1/ind2/ind3-reduction-20261016 | 0 | 1/7/2 | probes; Ind reductions actual in LeanFormal |
| k1k2-adoption-20261017 | 0 | 4 | probes; K1/K2 actual modules in LeanFormal |
| k1k2-boundary-reduction-20261016 | 0 | 7 | probes |
| k1k2-realization-20261016 | 5 | 16 | report/handoff; conditional realization |
| n8-20261018 | 47 | 2258 | huge N8 archive; see N8 docs, no paper Cor312 |
| n8-20261020 | 0 | 113 | probes/accept; no Cor312 construction |
| research | 0 | 0 | empty |
| paper_pages | 0 | 0 | empty |
| fclw-20261016 | 10 | 14 | ABCFrontier equivalent to ABC; no construction |
| api5-one-column-landing-20261016 | 7 | 46 | APT transport actual/conditional; no source q-pilot |
| abc-bridge-consistency-20261016 | 4 | 78 | probes of actual ABCBridge layers |
| cor312-to-abc-cards-20261016 | 0 | 3 | cards only |
| external/Takkun-IUT_LEAN | 3 | 37 modules | source-level conditional Cor312/Thm110 + negative trilenma |
| external/promachina-iut-lean-latest | many | huge | shadow structures; `cor312_lower_bound` is a field |
| external/PriestAmbrose-IUT-Corollary3_12-Lean | 1 | 1 | placeholder `sorry`; INVALID |

Other directories are probes, build logs, copied snapshots, or unrelated
survey repos; see the CSV for exact counts.

## 2. Q1 — what was actually achieved

### 2.1 Cor 3.12 logical skeleton (Takkun, external)

`tmp/external/Takkun-IUT_LEAN/IutLean/Multiradial/Cor312.lean`:

```lean
structure PilotVolumeData where
  Ω : Type; Γ : Type; vol : Ω → ℝ; vol_mono : Monotone vol
  thetaPilot qPilot hull : Ω
  hull_spec : ∀ g : Γ, g • thetaPilot ≤ hull
  containment : ∃ g : Γ, qPilot ≤ g • thetaPilot

theorem cor312 : P.negLogQ ≤ P.negLogTheta
```

Status: **source-level ACTUAL/CONDITIONAL (no sorry), UNVERIFIED here** (no current
olean). `trivialPilotVolumeData` is a nonempty but trivial witness. The entire deep
content is the `containment` field. It formalizes the *single-space* tautology;
`TwoSidedLink.lean` shows the honest two-space version has vacuity/non-isometry
trilenma.

`tmp/external/Takkun-IUT_LEAN/IutLean/Diophantine/Thm110.lean`:

```lean
theorem cTheta_ge_neg_one (P : PilotVolumeData) ... : -1 ≤ CTheta
theorem thm110_elementary_deduction ... : final Theorem 1.10 inequality
```

Status: source-level ACTUAL/CONDITIONAL (no sorry), UNVERIFIED; it is exact
elementary algebra from `CTheta ≥ -1` and the displayed constants, not a source
construction.

Negative results in same project (source-level, actual claims):
- `Multiradial/ThetaHullDichotomy.lean`: `no_lossless_theta_hull` — no lossless
  theta-hull transcription; lossy degeneracy verdict.
- `Multiradial/DisputedCore.lean`: `strict_collapse` — strict single-space data
  imply `False`.
- `Multiradial/TwoSidedLink.lean`: `relabeling_vacuous` (single-space comparison
  collapses to trivial hull inclusion), `link_not_isometric` (arithmetic
  normalization is not volume-preserving), `bounded_distortion_bounds_height`
  (bounded distortion bounds height), `twoSidedSupply_cTheta_ge_neg_one`
  (two-sided residual supply).
- `Multiradial/IdentificationAudit.lean`: honest vs identified transcriptions;
  `identified_qvol_incompatible`.

### 2.2 Actual project-side objects with olean/axioms

| object | file | evidence | caveat |
|---|---|---|---|
| IUT IV Step V theta bound | `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceStepVLambda.lean` | ACTUAL olean 545928 B; `arithmeticTuple_stepV_hull_le_paperBound_of_stepVLambda` axioms trio | conditional on `stepVLambda`; q-side `qSideSignedValueCondition` defined but not proved |
| Step V assembly | `FinitePlaceStepVAssembly.lean` | ACTUAL olean 1844432 B | local theta-side bound only |
| Step V j-invariant form | `FinitePlaceStepVJInvariant.lean` | ACTUAL olean 131088 B | consumes actual local j-invariant |
| Signed arithmetic-tuple certificate | `FinitePlaceIQHullSignedCertificateNonvacuous.lean` | ACTUAL olean 185208 B; axioms trio | `qSigned = min(hullLog,-1)`, `thetaSigned = log(mu unitRegion)`; NOT source q-pilot/CTheta; unit-region normalization assumption |
| Weighted q-pilot normalization | `tmp/sheaf/xif/paper/NativeGlobalQPilotNormalizedLogVolumeActual.lean` | ACTUAL olean 94384 B | native bad family; weighted formula; no source q comparison |
| Global q-pilot object | `tmp/sheaf/xif/paper/GlobalQPilotObjectActual.lean` | ACTUAL olean 126032 B | equals unweighted `sourceQPilotSignedLog`; not paper weighted q-pilot |
| S2807 theta-hull identity | `tmp/sheaf/xif/paper/S2807ThetaHullVolumeIdentityActual.lean` | ACTUAL olean 98000 B | identity only; SG3 upper gap remains |
| S2807 SG3a packet reduction | `S2807SG3aActual.lean` | ACTUAL olean 68800 B | reduces upper gap to packet log-volume |
| S2807 SG3b scalar | `S2807SG3bScalarActual.lean` | ACTUAL olean 60032 B | conditional on packet identity/scalar bound |
| S2800 ABC bridge | `S2800LineBundleCor312BridgeActual.lean` | ACTUAL olean 95472 B | conditional on `S2800GlobalData` + per-eps `S2800EpsData`; G0-G2 missing |
| S2717 Cor312 target | `S2717Cor312FullTargetActual.lean` | ACTUAL olean 91472 B (target Prop) | `S2717UpperGap` not proved |
| S2715 CTheta algebra | `S2715CThetaPaperScaleActual.lean` | ACTUAL | reduces CTheta lower bound to upper inequality |
| S2752 hweightvol | `S2752FinalHweightvolActual.lean` | ACTUAL olean 139480 B SHA 2318A7BF... | actual arithmetic comparison, not region/height |
| S2812 IsStack | `tmp/sheaf/xif/paper/S2812IsStackActual.lean` | ACTUAL olean 200952 B SHA E0757316... | scheme-representable pseudofunctor only |
| D6 F6 complete | `S2848D6F6CompleteActual.lean` | ACTUAL olean 14640 B SHA 5C35953D... | actual D6 fixed geometric realization |
| S2812 source-Haar no-go | `S2812DegreeFaithfulSectionActual.lean` | ACTUAL olean 41944 B | no degree-faithful section from source-Haar datum |
| S2813/S2786/arithmetic37 | historical | intermediate | **INVALID for ClauseC** (F=Q(i), E[6] not rational); correct F6 route |

### 2.3 Actual but conditional bridge / target objects

- `S2800LineBundleCor312BridgeActual` is the cleanest actual ABC bridge, but it
  consumes `S2800GlobalData` and `S2800EpsData` (`hregion`, `hheight`). G0/G1/G2
  are not constructed; G2 is ABC-hard.
- `S1000FinalCor312AssemblyActual`/`S1024FinalCor312Actual` are conditional on
  explicit finite Step-XI certificate/link inputs. They are assembly, not proof.
- `sourceProcessionStepXIXifInclusionResidual` is an actual interface obligation,
  not a carrier; literal xi-f closes degenerately on nonnegative carriers.

## 3. Q2 — failed / refuted routes

| route | evidence | reason |
|---|---|---|
| Paper-level 3.12 via fixed `S1487Cand.q` (S2030/S1944) | `coord/paper-level-target-audit-20261102.md` | q does not depend on same input; proof uses `log 5>1` and `a0≤1`, not Θ-link |
| S2040 scalar/structural target | same audit | Θ defined as q^(1/(2l)); `logVolumeComparison`/identification stored as fields; `S2040FirstMissing` no inhabitant |
| P6/C6 target | same audit | different inequality: positive `log mass` vs negative `-|log Θ|`; P6 weaker/automatic, not paper 3.12 |
| Raw line-bundle region volume | `coord/GAPS_ABC.md` discarded | inert p^2; raw region not correct; must use half-normalized W |
| Source-Haar carrier | `S2812DegreeFaithfulSectionActual` ACTUAL no-go | no degree-faithful section from source-Haar datum |
| Raw `sourceHullVolume` upper | `sourceThetaBound_unsat_of_degreeFaithful` ACTUAL | under `hdeg` hull volume is `⊤`; no real θ upper. Conditional on hdeg, not absolute |
| `PaperThetaHullEqQPilotActual` | `PaperThetaHullEqQPilotAudit.md` | constant/diagonal tuple surrogate; wrong F_l^x component indexing; Haar exponent `card(SourceVolumeIndex)` not justified; circular |
| `Cor312CarrierRealizationSpec` four-field package | `cor312-gap-dictionaries-20261016/e2-report-section.md` | (a)+(c) and (c)+(d) jointly refutable; no inhabitant; fixed (c) plus direct volume card needed |
| Card-QCMP/Card-AMPL direct instantiation | `QCMPComparisonSupply`/`CardAMPLThetaBoundSupply` | targetSigned/realVolume_le_theta are fields; no source instantiation; singleton supply trivial |
| Card-HULLREAL signed wrapper | `CardHullRealSignedLogVolume` | `qSigned≤hull` is a hypothesis; `thetaSigned=0`; under hdeg collapses; no source q |
| Pointwise `S2882A6Q.IsStack` (hQ) | `S1971ActionStackificationActual` §4; `S2870` audit | pointwise action groupoid is only a prestack; stackification separate; hQ likely false as stated |
| `S2996` full stack witness | S2996 olean actual only for core | full witness requires `IsPrestack`+`IsStack` fields; no construction; S3009 trivial total-space IsStack has wrong fibers |
| `S2958` half-IQ-hull certificate | S2958 ACTUAL olean | q=-1, theta=hull+1/0; tautological; not CTheta |
| `S2953` CTheta certificate | S2953 ACTUAL olean | fields `hCTheta : CThetaPaper = thetaLogVolume/|log q|` and `hupper : thetaLogVolume ≤ CThetaPaper*|log q|`; hupper forced by hCTheta; conditional tautology |
| S2935/J-height route | `S2935HeightLeProcessionActual` | target is a Prop; no proof; S2945AdditiveBound = `ABCHeightWeightAdditiveBoundV2`; bridge Props unproved; not paper Cor 3.12 |
| Takkun `PilotVolumeData` as source | Takkun Cor312 | `containment` is a field; trivial witness; single-space tautology; `TwoSidedLink` negative results |
| `fclw` ABCFrontier | `abcFrontier_iff_abcConjecture` | equivalent to ABC; no frontier construction; cannot close by naming |
| `promachina` Stage1 shadows | `IUTStage1IUTIVAlgebra.lean` | `cor312_lower_bound`/`explicit_estimates_to_theorem110_rhs` are structure fields; actual algebra from assumptions, not source |
| PriestAmbrose external Cor312 | `src/.../Cor312.lean` | placeholder Nat skeleton with `sorry`; INVALID |

## 4. Q3 — reusable / portable

### Direct reuse (actual, project tree)

1. `FinitePlaceStepVLambda`, `FinitePlaceStepVAssembly`, `FinitePlaceStepVJInvariant`
   — actual local Step V theta bound; reuse rather than re-prove S2936 analogue.
2. `NativeGlobalQPilotNormalizedLogVolumeActual` — actual weighted native q-pilot
   normalization; reuse for the q side.
3. `FinitePlaceIQHullSignedCertificateNonvacuous` — actual signed certificate
   template; reuse only as a signed-measure wiring, not as paper CTheta.
4. `S2807ThetaHullVolumeIdentityActual`/SG3a/SG3b — actual theta-hull identity
   and reductions; reuse and target the missing packet formula.
5. `S2800LineBundleCor312BridgeActual` — actual conditional ABC bridge; reuse
   once G0/G1/G2 are supplied.
6. `S2812IsStackActual`, `S2848D6F6CompleteActual`, `S2752FinalHweightvolActual`
   — actual stable infrastructure.
7. `coord/S2804_COR312_INVENTORY.md`, `coord/GAPS_ABC.md`, `coord/paper-level-target-audit-20261102.md`,
   `coord/ROADMAP-2026-11-02-REVIEW.md`, `tmp/sheaf/gap-exploration-20261030` —
   historical inventories and no-go records; reuse as audit evidence, not as proof.

### Portable logic (source-level, needs compile in our toolchain)

1. Takkun `Cor312.lean` + `Thm110.lean`: small Mathlib-only logic skeleton;
   port `PilotVolumeData`/`cor312`/`thm110_elementary_deduction` as a *spec* or
   cross-check, not as source theorem.
2. Takkun `TwoSidedLink.lean`, `ThetaHullDichotomy.lean`, `DisputedCore.lean`:
   excellent negative controls/vacuity checks; port only as audit lemmas.
3. `promachina` Stage1 explicit `CTheta` formula and coefficient estimates:
   useful algebra/reference; the theorem fields are assumptions.

### Do not reuse

- `PriestAmbrose` Cor312 (sorry placeholder).
- `PaperThetaHullEqQPilotActual` (invalid/circular).
- `Cor312CarrierRealizationSpec` as a package (jointly refutable).
- `S2953`/`S2958` as CTheta estimates.
- `S2996` full witness / S3009 total-space as A6 quotient stack.
- Old S2786/arithmetic37 for ClauseC.

## 5. Q4 — shortest feasible path

### Path 1 (shortest actual-to-paper, recommended): IUT IV Step V chain

```text
FinitePlaceStepVAssembly / StepVJInvariant (ACTUAL)
  + FinitePlaceStepVLambda (ACTUAL theta bound)
  + NativeGlobalQPilotNormalizedLogVolumeActual (ACTUAL q normalization)
  -> qSideSignedValueCondition + procession average
  -> local Step V bound + q-side comparison
  -> S2717UpperGap / CTheta upper.
```

Missing objects:
1. actual `qSideSignedValueCondition` (`qSigned = -|log q|`, q from same source);
2. procession-normalized average over j of the per-label Step V bound;
3. final real inequality with paper constants;
4. identification of the q-pilot used in Step V with the weighted global q-pilot.

Closest implementation: `FinitePlaceStepVLambda.lean:428` (theta bound),
`NativeGlobalQPilotNormalizedLogVolumeActual` (q magnitude), `FinitePlaceStepVAssembly`
(local volume). Why shortest: the theta side is already actual; only the q-side
identification/averaging is missing.

### Path 2 (paper-faithful, deeper): C1 `XiEToXiFOutputReadoutProjection`

```text
fixed admissible C
  -> q-pilot mark through U2K2/IPL
  -> membership in restricted final-evaluation output family P_C
  -> exact Q_C ∈ {nu_C(D)} or signed ∀ε ∃Dε, Q_C-ε ≤ nu_C(Dε)
  -> hull upper bound for every D
  -> Q_C ≤ h_C (Cor 3.12 xi-f).
```

Missing object: no source constructor for the q-mark -> sQ3 hull-determinant map.
Closest: `tmp/sheaf/n8/closure/C9-U2K2-SQ3-MARKED-TRACE-20261026.md` and
`C9-C1-HANDOFF-SUMMARY-20261026.md`; no Lean inhabitant.
This is the historically correct paper bridge but is not shorter than Path 1.

### Path 3 (S2807 paper theta hull route)

```text
S2807_thetaHullVolume_eq_haarRegion (ACTUAL)
  -> S2807C3TensorPacketLogVolumeFormula (MISSING packet identity)
  -> S2807SG3b scalar bound
  -> S2717UpperGap
  -> PaperCor312Full (conditional on q normalization + xi-f).
```

Missing: exact C3 tensor packet log-volume formula, q_Tate identification, xi-f
instantiation. Closest: S2807 SG3a/SG3b; S2804 inventory section SG3.

### Path 4 (not recommended): signed floor certificate

`FinitePlaceIQHullSignedCertificateNonvacuous` is actual, but its q is
`min(hull log,-1)` and its theta is `log(mu unitRegion)`, not the paper q-pilot/CTheta.
Use it as a signed-carrier template only, not as target.

## 6. Q5 — status classification

### ACTUAL (verified olean + axioms trio here)

- `FinitePlaceStepVLambda` (theta bound), `FinitePlaceStepVAssembly`, `FinitePlaceStepVJInvariant`;
- `FinitePlaceIQHullSignedCertificateNonvacuous` (signed floor certificate);
- `NativeGlobalQPilotNormalizedLogVolumeActual`, `GlobalQPilotObjectActual`;
- `S2807ThetaHullVolumeIdentityActual`, `S2807SG3aActual`, `S2807SG3bScalarActual`;
- `S2800LineBundleCor312BridgeActual`, `S2717Cor312FullTargetActual` (target),
  `S2715CThetaPaperScaleActual`, `S2752FinalHweightvolActual`;
- `S2812IsStackActual`, `S2848D6F6CompleteActual`, `S2812DegreeFaithfulSectionActual`;
- `S2932CorrectedCuspConsumerActual`, `S2908CorrectedSActual`, `S2927Completion`,
  `S2928CorrectedT`, `S2934CorrectedT` (conditional assembly; see caveat);
- `S1964QuotientStructure`/`S2043D9FullActual` quotient audit (not construction).

Caveat: the corrected A6 chain is actual only conditional on hQ/D/W/I; hQ is
likely false (pointwise Q is only a prestack). It is not a source-data construction.

### CONDITIONAL ACTUAL

- Takkun `PilotVolumeData.cor312`, `cTheta_ge_neg_one`, `thm110_elementary_deduction`
  (source-level, no current olean);
- `S2800LineBundleCor312BridgeActual` (G0-G2 inputs);
- `S1000FinalCor312AssemblyActual`/`S1024FinalCor312Actual` (certificate/link inputs);
- `S2927Completion`/`S2928CorrectedT`/`S2934CorrectedT` (hQ/D/W/I inputs);
- `S2933Certificate` (height/theta inputs);
- `S2935HeightLeProcession` (unproved Prop).

### STATEMENT ONLY

- `S2717UpperGap`/`PaperCor312Full` (target);
- `S1971QuotientStack`/`S2893A6QEffectiveDescent`/`S2995A6StackWitness`;
- `S2945AdditiveToProcessionBridge`/`ProcessionToAdditiveBridge`;
- `S2951ThetaUpperTarget` (only trivial C=0 estimate);
- `S2907ClauseFCorrected`/`S2926Inputs` (obligation bundles).

### REFUTED / NO-GO

- raw source-Haar carrier: `S2812_sourceHaarActual_no_degreeFaithfulSection`;
- raw `sourceHullVolume` upper under hdeg: `sourceThetaBound_unsat_of_degreeFaithful`;
- `PaperThetaHullEqQPilot` diagonal surrogate: invalid;
- `Cor312CarrierRealizationSpec` four-field package: jointly refutable;
- single-space/two-side routes: Takkun `strict_collapse`, `relabeling_vacuous`,
  `link_not_isometric`;
- pointwise Q.IsStack: `S1971`/`S2870` prestack obstruction;
- S2953/S2958 certificates: tautological;
- `fclw` ABCFrontier: equivalent to ABC, not a proof;
- old S2786/arithmetic37 for ClauseC: invalid F=Q(i).

### UNVERIFIED EXTERNAL

- Takkun source-level claims (`lake build` green in its ledger, no olean here);
- promachina Stage1 shadows (no olean here);
- PriestAmbrose (invalid placeholder);
- lana/tempered-fundamental-groups external libraries (survey only, not IUT source).

## 7. Current repair notes

- S2922/S2930/S2906/S2948 were dispatched for repair by Lead; they are current
  target work, not historical actuals. Do not cite them as actual until fresh
  compile + olean + axioms trio.
- S2936 remains kummer sole-owner; this report does not edit it.

## 8. Source anchors

- `coord/S2804_COR312_INVENTORY.md` — actual/missing Cor 3.12 inventory.
- `coord/GAPS_ABC.md` — G0-G12 gaps and discarded routes.
- `coord/paper-level-target-audit-20261102.md` — why S2030/S2040/P6 are not paper-level.
- `coord/ROADMAP-2026-11-02-REVIEW.md` — five hard blockers, D6/D9/D5/H1.
- `coord/S2807_UPPERGAP_ROUTE.md` — SG1 actual, SG3 packet missing.
- `tmp/sheaf/gap-exploration-20261030` — source-object alignment report.
- `tmp/sheaf/n8/closure/C9-C1-HANDOFF-SUMMARY-20261026.md` — C1 exact missing.
- `tmp/sheaf/n8/closure/C9-U2K2-SQ3-MARKED-TRACE-20261026.md` — no q-mark->sQ3 map.
- `tmp/external/Takkun-IUT_LEAN` — logical skeleton and two-sided negative controls.
