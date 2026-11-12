# CANONICAL GATE DRAFT V2 — CORRECTED SCOPE (NON-CANONICAL)

**Status:** DRAFT (Lead assignment; gate table itself remains FROZEN — this file is **NOT** the
canonical gate table and does not change gate status). Author: 拉蒂/lattice.
**Pins:** registry **14041** / gate **in flux** / record **18800**; L8 frozen; no registry edits.
**Date:** 2026-11-10.

## 1. COVERAGE LINE (canonical wording, verbatim)

> **'F=ℚ component delivered + full-Q̄ reduction named (not complete)'**

Use this line in every coverage/scope note. No closure claim beyond this line.
Gate verdict remains **NOT PASSED**; binding **HOLD**; FINAL ROWS suspended.

## 2. DELIVERED GREEN COMPONENTS (restated scope; evidence recorded by owner audits)

All items below are CITABLE per their audit records unless stated otherwise; hashes/sizes are
those recorded in AUDIT_LEDGER / owner audit files. **Green component ≠ paper obligation closure.**

### 2.1 Restated interfaces / corrected target (C-point)
| component | evidence | status |
|---|---|---|
| `RestatedLemma24InterfaceActual` | mainline A286: EXIT0 **5255B**, **CITABLE 9 decls**; `Mzk1Lemma24Target` (C-point/specialSet/unramified), `CVInvariant`, `CVCompositionLawStatement`, `SpecialSetPreservationStatement` | FRESH GREEN (audit S3248: C-points PASS, no targetSet/unramifiedAt loophole PASS, degenerate-witness check PASS, vocabulary harmonization pending) |
| `RestatedLemma24CVLawActual` | S3255: **CITABLE 5 decls 3918B sha 9EE41ECD** (probe_ok, zero sorry): `criticalValuesOverC_eq` (C-point CV = ported TauCeti `q.criticalValues ℂ`); **CVCompositionLaw PROVED**; **SpecialSetPreservation PROVED**; CVCompat PROVED | GREEN — discharges CV-accounting hypotheses of `s3135_CVInvariant_comp` |

### 2.2 Induction / 2.2 interface layer (corrected)
| component | evidence | status |
|---|---|---|
| `Mzk1Lemma22StepInterfaceQActual` | S3249: **CITABLE 4 decls 2698B sha C74EE6FF** (probe_ok); new step interface with explicit Q-membership; named TODO `step_interface_of_hypotheses_statement` | GREEN interface (named TODO was discharged by 2.2.2) |
| `Mzk1Lemma22StepInterfaceQProofActual` | S3252: **CITABLE 1 decl 3831B sha B480D0F5** (probe_ok, zero sorry): `step_interface_of_hypotheses_proof` PROVED (phi=gPoly D; targetS = S.image (polyMapPoints gPoly); H-on-image via `hyp_preservation_full` S3238; card decrease via `card_image_gPoly_lt`; rational-point unramified via `gChoice_unramified`) | GREEN — bugfix #2 proof landed; old `Mzk1Lemma22InductionActual` signature legacy/deprecated |
| `Mzk1Lemma22FullShapeHelpersActual` | S3249: **CITABLE 9 decls 3403B sha DD987A8A** (probe_ok): `critValues_comp_subset` + `critValues_comp_subset_union` PROVED; BaseGoodData + `baseGoodPoly (c*X)` + degree/derivative PROVED; CritIn01 over ℂ; no True/toy | GREEN helper layer |

### 2.3 L2.3 normalization + HPRES / conditioned gate (2.2 numeric layer)
| component | evidence | status |
|---|---|---|
| `Mzk1Lemma23NormalizationActual` | S3229: **CITABLE 6 decls 6520B sha B21C1493**: normMap t/(z−λ); bounds; `s3135_normalization_exists` PROVED | GREEN |
| `Mzk1Lemma24NormalizationTransferActual` | S3230: **CITABLE 21 decls 12033B sha 2E673AC3** (probe_ok, zero sorry): P1Morphism transfer laws, `transfer_statementShape`, P1Affine inverse laws | GREEN (L2.3 evidence) |
| `Mzk1Lemma22HypPreservationActual` | S3233: **CITABLE 14 decls 6825B sha CB0F53B6** (probe_ok, zero sorry): HPRES components 1-4 PROVED (Even-n reduction, target memberships/positivity/avoids) | GREEN |
| `Mzk1Lemma22HypPreservationSeparationActual` | S3237: **CITABLE 4 decls 9136B sha C86E19B8** (probe_ok, zero sorry): separation (5) PROVED ⇒ HPRES 1-5 COMPLETE, no named residue, canonical hypotheses-preservation unconditional | GREEN |
| `Mzk1Lemma22HypPreservationCanonicalActual` | S3242: **CITABLE 4 decls 4111B sha 7E575EA9** fresh: canonical_hypotheses_preserved + card collapse | GREEN |
| `Mzk1Lemma22ConditionedActual` | S3238: **CITABLE 2 decls 2054B sha 60FA5B9B** (probe_ok, zero sorry): `hyp_preservation_full` + `hyp_preservation_of_hypotheses` PROVED = conditioned h22 step | GREEN |

### 2.4 Möbius Q/C + CV bridge + CritValue staging
| component | evidence | status |
|---|---|---|
| `Mzk1MoebiusP1Actual` (Q-typed source) | S3253: **CITABLE 12 decls 7832B sha 4D63BB55** (probe_ok, zero sorry): matrix composition det mult; mapPoints_nonconstant case split (pole/infinity conventions verified); derivativeNumerator ≠ 0 ⇒ CV=∅; specialSetQ mapsTo; moebiusInversion permutes specialSet | GREEN Q-typed source (A305 layering) |
| `Mzk1MoebiusP1C` (C-typed variant) | S3256: **CITABLE 14 decls 6995B** (probe_ok) — closes A297 C-flag | GREEN; layering: design 9329B sha 18E57C92 unique Q-typed source; qpilot extension separate; C-file distinct (no dup/cycle) |
| hull `CVLawProof` | 3217B — **redundant duplicate counted once vs S3255** | not counted separately |
| `RestatedLemma24CVLawActual` | S3255 (see §2.1) | GREEN |
| CritValue staging | S3257: `aeval_cast_eval` PROVED; **`CritValueInImageStatement` = NAMED item (i)** (5-row TODO ledger, no fake theorem); awaits hull `BelyiCvBridge` (4952B, red/fixing) | PARTIAL staging — item (i) NAMED |

### 2.5 Consumer design (conditional, NOT closure)
| component | evidence | status |
|---|---|---|
| `Mzk1Thm25P1CompositeConsumerDesignActual` | S3254/A301: **CITABLE 12 decls**; A305 re-verified WITH probe EXIT0 **8715B**, src **90123C46** / olean **AC95FFC6**; earlier pin 8098B/90638394. `P1CompositeRealConsumerTarget` = C-point version; `P1CompositeConsumerInputs/Statement` name exact upstream needs; hullInterfaceNeeds 6; availableMoebiusAssets 8 | **STATEMENT/DESIGN ONLY — NOT closure**; consumer LAST |

### 2.6 Supporting evidence / records (not gate rows)
- 2.4 (G)(F)(D)(M) interface evidence (S3223) — 17 files CITABLE per owner audit; notes named
  residuals M1a/M1b/M2 etc. under **old target**, historical/progress only.
- Assembly skeleton `Mzk1Lemma24Assembly` S3232 (CITABLE 7 decls 5215B 2944F69C) — **skeleton only**,
  old `Mzk1Lemma24Goal` degenerate; requires retargeting, not closure.
- Rational base provider `Mzk1Lemma24BaseProvider` S3236 (CITABLE 3 decls 6893B 67175237) — old target;
  restated beta-avoiding base provider OPEN (see named inputs).
- Integrity correction S3244 (five defects; gate invalid as constructed), assignments S3246,
  scope decision S3258 citable; S3178 gap list **30978B**; audits S3249-S3257 citable.
- Deprecation/consumer/CV bridge reference: `coord/CORRECTED-TARGET-XREF.md`;
  mainline `coord/OLD-TARGET-CONSUMERS-ANALYSIS.md`.

## 3. NAMED INPUTS (not proved; must remain named, proved := false)

| # | named input | scope / paper source | notes |
|---|---|---|---|
| 1 | `BetaAvoidingBelyiBaseInput` | restated rational base provider: β-avoiding Belyi/polynomial base construction over ℚ for the corrected C-point target | restated base provider attempt in progress; old BaseProvider targets degenerate goal |
| 2 | `Mzk1Lemma22BaseProviderStatement` | base provider at measure (0,0) under corrected target | old version built on degenerate goal; restated statement required |
| 3 | `CPointCVInImageStatement` | item (i) C-point CV-in-image (C-strengthened Lemma 2.1(b)); awaiting hull `BelyiCvBridge` | S3257 named item (i) with 5-row TODO ledger |
| 4 | `CorrectedStepProviderPaperInput` | corrected step provider (f0-measure-decrease bookkeeping paper lines 195-203 + transport composition under CV invariant) | S1a/S1b/S2/S3/S2-i proved pieces available; provider statement itself named |
| 5 | `CorrectedAssemblyPaperInput` | corrected nested-induction assembly over restated target/CVInvariant (paper 179-206) | old assembly skeleton retarget pending |
| 6 | `AlgebraicNestedInductionInput` | algebraic nested induction over Q̄ (class-B) for full-Q̄ reduction (paper 179-206) | named in A313 scope decision |

Plus paper-level named inputs already recorded in gate context: **[Mzk1] GeometricCore deep input**
(GeometricCoreWitness free Prop fields defect), **AbsTopIII05 deep named**, class-B
infinite-Galois fixed field, 2.3 Möbius over Q̄/ℂ, class-B algebraic nested induction (same as #6).

## 4. REMAINING IUT GATE ITEMS

1. **H6 PARTIAL** — GenEll transfer wired only via explicit GeometricCore hypothesis
   (`GenEll10bH6Mzk1Wiring`, `Hull07H6Interface` conditional, `Hull11H6Mzk1Upgrade` with named
   reduction hypotheses). Not closure.
2. **Thm25 binding HOLD / Thm2.5 unconditional NOT claimed** — A277 defect 4: thm25_wiring
   conclusion uses hcore only; GeometricCoreWitness free Prop fields. Binding file on HOLD
   (`tmp/xif_hold_files.txt`).
3. **Deep inputs** — [Mzk1] GeometricCore; AbsTopIII05; infinite-Galois fixed field class-B;
   Q̄-level 2.3 Möbius/CV; algebraic nested induction class-B.
4. **L7/L8** — EtTh/Frd statement layers citable; L8 IUT IV §1 display/Cor 3.12/GeometricCore
   assembly **FROZEN** until full-page conditions + real consumer.
5. **Ported/non-gate** — ported assets and paper red-tracked items are NOT gate rows
   (asset record only); no gate count change.

## 5. ONE-TIME REPUBLISH TEMPLATE (only after conditional wiring green + Lead approval)

When (and only when) conditional wiring is green and Lead/mainline issue FINAL ROWS:
1. Create a NEW clean gate-table Lean file under `tmp/sheaf/xif/paper/` (new path; keep rows
   compact <1800 chars; do NOT edit frozen historical gate files `IUTExternal30/31/32/33/34*`).
2. Insert **§1 coverage line verbatim** as a top-level row/note.
3. Insert **delivered components** as rows with fresh **EXIT0 SIZE / checker CITABLE / probe_ok /
   src sha / olean sha** (re-verify each with `tools/xif_citable_check.ps1 -File <f> -Probe <p>`;
   stale pins superseded only by a fresh checker run).
4. Insert **named inputs** as explicit rows with status `named (proved := false)`; never as proved.
5. Insert **remaining gate items** (H6 PARTIAL, deep inputs) and the verdict:
   **GATE NOT PASSED** unless Lead explicitly upgrades; no "Thm2.5 unconditional" claim while HOLD.
6. History rows: old gate paths = corrupt/frozen history; duplicate backups non-canonical;
   old-target files marked DEPRECATED-UNDER-CORRECTED-TARGET (xref).
7. Run **checker + probe** on the new file; report fresh pin values to shehdd for one audit.
8. Only after shehdd audit + Lead approval may the "canonical" label move; ledger/STATE updated
   with pins (registry 14041 / gate = new pin / record 18800; L8 frozen; no registry edits).
9. While HOLD persists: do NOT queue/un-HOLD binding files; un-HOLD only by explicit Lead
   decision after real consumer + restated full gate.

**Republish preconditions (all required):** conditional wiring green (CV law + C-point CV-in-image
+ corrected providers + assembly + real consumer 2.4∘2.3∘2.2) **AND** Lead-approved FINAL ROWS
**AND** shehdd audit slot; otherwise keep this draft non-canonical and gate frozen.

---

*Draft only — non-canonical. Prepared by 拉蒂/lattice under gate freeze; no gate-table writes,
no Lean edits, no closure claims. Evidence citations are owner audit records (S3229-S3258,
A277-A316); hashes recorded as reported by owners and subject to re-verification at republish.*

---

# A321 INTEGRATION (mainline feed coord/IUT-PREREQUISITES-REMAINING.md)

**Feed status (mainline A321):** IUT prerequisite objects NOT complete. Corrected 2.2/2.4 restatements exposed the ALGEBRAIC Qbar layer as named; IUT gate remaining = **H6 PARTIAL + deep inputs**. Coverage line canonical (see §1).

## A. GATE ROWS L0-L8 (authoritative current status)

| Layer | Status | Evidence | Remaining for PASS |
|---|---|---|---|
| L0 curves/function fields | CLOSED/PASS | E1 defs CITABLE; AG01/02 | none |
| L1 divisors/height-weight | CLOSED/PASS | tree asset + AG03 | none |
| L2 cohomology | CLOSED/PASS | AG05 Cech CITABLE; AG_FLT_CechPromotion | none |
| L3 RR/Serde | CLOSED/PASS (ported) | AG_FLT_Promotion/RiemannRoch/CanonicalDivisor/Serde promotions CITABLE; ported assets non-gate | none |
| L4 Belyi/finite maps | PARTIAL | Mzk1 2.1 ALL PROVED; 2.4 F=Q component (base m(S)=0 + rational Belyi existence supported S3236/S3229/S3230/S3237/S3255/S3232); FiniteMapData resolved | FULL Qbar layer named: (D) finite-Galois PROVED + infinite fixed field class-B + 2.3 Moebius over Qbar/C + AlgebraicNestedInductionInput class-B |
| L5 GenEll | PARTIAL (statement layer citable) | GenEll05 Thm2.1 (i)=>(ii) PROVED; GenEll10b H6 wiring; GenEll15 GeometricCoreAssembly; GenEll16 BelyiExistence; GenEll17 BelyiPair bridge; GenEll13/14 etc. | GenEll Thm2.1 (ii)=>(i) consumer needs noncritical Belyi existence (Lemma 2.2 restated target conditional F=Q) + H6 precise GeometricCore; consumer of corrected 2.4 not yet wired |
| L6 AbsTopIII | PARTIAL | 01/03/07/08/09 complete citable; H1-H5/H7 rows closed w/ class-B leftovers; H6 PARTIAL (GenEll transfer; Hull11 upgrade citable; reduction hypotheses named) | H6 precise-ification (assigned 胡尔: Mzk1GeometricCorePreciseActual); AbsTopIII05 deep named input remains |
| L7 EtTh/Theta | PARTIAL | EtTh07/08/09/10/11/12/13 citable; theta power-kernel anti-monotonicity PROVED | realization deeper rows class-B named |
| L8 IUT IV section1 | FROZEN/NOT PASSED | S3171IUTIVSection1{Statement,Estimates,Display,Inputs}+UniformHeightConsumer green; thm110 display conditional on inputs | display/Cor312 assembly requires L0-L7 self-write gaps close + inputs (b) uniform height-vs-volume etc.; remains FROZEN |

## B. RATIONAL BASE-ONLY vs NAMED QBAR REDUCTION ROWS (structure per A321)

**Layer R (F=Q) = delivered component** (rational base m(S)=0 + rational Belyi existence; conditional assembly skeleton). See §2-§3 above for the per-component hashes.

**Layer A (Qbar, paper 2.4 lines 144-160, proof 163-206) = NAMED inputs, NOT complete:**
1. `AlgebraicClosureFixedFieldPaperInput` - infinite Galois fixed field (class-B).
2. `AlgebraicNestedInductionInput` - paper 179-206 m/d descent step (class-B NEW).
3. `BetaAvoidingBelyiBaseInput` - class-B; BLOCKED (no beta control in TauCeti Belyification; qpilot searching upstream/ported).
4. `CorrectedStepProviderPaperInput` - corrected step provider.
5. `CorrectedAssemblyPaperInput` - corrected assembly over restated target/CVInvariant.

Also: 2.3 Moebius separation over Qbar/C - Q-typed lib + C-typed variant delivered (S3253/S3256); separation PROVED (S3237) at rational/measure level; **Qbar application wiring NOT built**. Measures m/d meaningful only for algebraic points; rational-only m(S)=0 trivial base case.

## C. DEEP INPUTS / CLASS-B NAMED (IUT-side)
1. AbsTopIII05 deep construction (paper input; named).
2. H6 GeometricCore: Mzk1GeometricCoreWitness fields free Props (RealStructure:59) - precise-ification required; Hull11/Hull13/GenEll15 consume conditionally.
3. H5 q-side O^x stabilization (class-B named).
4. H7/Ob9 arbitrary-iterate bound (deep class-B; Hull12 one-sided only).
5. EtTh/theta realization deeper rows (class-B named).
6. IUT IV section1 inputs: (b) uniform height-vs-volume / region-relative-to-hull-and-weight etc. (L8 frozen until L0-L7 close).

## D. IMMEDIATE ASSIGNMENT QUEUE (A321, matching Lead A320)
- 胡尔: H6 precise-ification Mzk1GeometricCorePreciseActual (precise GeometricCoreStatement + reduce free Prop fields; consume GenEll15/Hull11/Hull13).
- 齐波: search upstream/ported beta-avoiding Belyi existence (unlock BetaAvoidingBelyiBaseInput class-B) + C-typed CV integration.
- 拉蒂 (this file): gate table corrected-scope draft (base-only rational rows; named Qbar reduction rows; coverage line verbatim).
- 司徒: conditional 2.2 induction (Mzk1Lemma22InductionProofActual hbase/hstep/CPointCVInImageStatement -> InductionStatement -> target_of_induction) + item (i) via BelyiCvBridge declarations.
- 艾比: conditional 2.4 base provider (Mzk1Lemma24BaseProviderRestatedActual with BetaAvoidingBelyiBaseInput -> Target) + assembly conditional chain + Layer A AlgebraicNestedInductionInput statement file.
- 史蒂: scope notes + consumer LAST; wire Qbar layer only after named layers available.
- 谢德/拉蒂: audit + xref updates; no closure claims.

## E. RULES (from A321)
- GATE NOT PASSED; binding HOLD; FINAL ROWS suspended; no closure claims under rational-only scope.
- Any coverage statement must use: 'F=Q component delivered + full-Qbar reduction named (not complete)'.
- Pins: registry 14041 / gate in flux / record 18800; L8 frozen; no registry edits.

*A321 integration appended by 拉蒂/lattice; draft remains NON-CANONICAL; no gate-table writes.*
