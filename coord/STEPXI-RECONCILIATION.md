# STEP XI — RECONCILIATION of existing formalizations with latest green results (A834, shehdd)

Status: 2026-11-12. Scope: `LeanFormal/IUT/IUTI/HodgeTheater/*` (25 files),
`LeanFormal/IUT/IUTII/Theta/*` (9), `LeanFormal/IUT/IUTIII/Corollary312/**` (90, incl.
`StepXI/` 83 and `StepXI/HolomorphicHull/` 51).  Our green results live in
`tmp/sheaf/xif/paper/` and `LeanFormal/IUT/.../Theorem311|StepXI/...`.

## A. All `VerificationStatus.pending` obligations found (14)

| id | file:line | note (short) | our green support | status |
|---|---|---|---|---|
| `IUT-I.hodge-theater-source-existence` | `IUTI/HodgeTheater/SourceObligations.lean:24` | SourceTheaterRealization from arbitrary D; three routes blocked | none (no green construction) | **MISSING** |
| `IUT-III.IPL` | `IUTIII/Corollary312/Obligations.lean:8` | relate output to q-pilot prime strip; depends Thm3.11 output, Ind1/2 | `SourceLinkFactorization` interface (`Theorem311/SourceKummerEvaluationArrows.lean:418`), `kummerMap_thetaOne` (`Mzk1KummerTransportActual`, green) | **PARTIAL** (interface + Kummer realization green; actual factorization inhabitant MISSING) |
| `IUT-III.SHE` | `.../Obligations.lean:15` | expressibility in fixed one-column structure; depends IPL, Ind3 | `SourceLocalizationExpressible` def + `sourceLocalizationExpressible_of_equiv` (`Theorem311/SourceArithmeticHolomorphicLanding.lean:292,305`); `SourceSHETransportLaws.lean` | **PARTIAL** |
| `IUT-III.APT` | `.../Obligations.lean:22` | algorithmic parallel transport with invariants | `SourceAPTStatement`/`SourceAPTSlotAssembly` (`StepXI/APT.lean:308,332`); `Mzk1StepXIMinimalStatementShaActual` | **PARTIAL** (slot assembly green; actual supply pending id below) |
| `IUT-III.theorem-3.11.5` | `.../Routes.lean:56` | intermediate checkpoint hull+det/descent, Thm3.11→3.11.5 via APT+IPL | h_V/scaled work: `Mzk1Paper312ExplicitActual`, `Mzk1PaperNormDeficitActual`, `Mzk1HVLemmaActual`, `Mzk1HullLogVolumeFormulaActual`, `Mzk1ScaledPaper312Actual` | **PARTIAL** (h_V algebra/volume side green; source construction not) |
| `IUT-III.theorem-3.11.5-to-corollary-3.12` | `.../Routes.lean:75` | common-container comparison of q- and Theta-packets | `Mzk1StepXIFormalizationAttemptActual` (choice-existence gap), `Mzk1ScaledClosingShaActual`, `Mzk1Paper312StatementActual` | **PARTIAL** (volume normalization/statement green; choice-existence = A832 missing lemma) |
| `IUT-III.arithmetic-teichmuller-corollary-3.12-route` | `.../Routes.lean:87` | Joshi arithmetic Teichmuller route | none | **MISSING** |
| `IUT-III.sarkisyan-erdos-kac-route` | `.../Routes.lean:105` | Sarkisyan Erdős–Kac route | none | **MISSING** |
| `IUT-III.route-comparison-audit` | `.../Routes.lean:123` | compare 3.11.5 / arithmetic-Teichmuller routes | `coord/STEP-XI-SPEC.md` (spec only) | **MISSING** (audit doc exists; no Lean) |
| `IUT-III.source-APT-transport-supply` | `StepXI/APT.lean:460` | actual inhabitant of `SourceAPTStatement S A A'` (Card APT) | `SourceAPTStatement` def + slot assembly; `Mzk1KummerTransportActual` | **PARTIAL** |
| `IUT-III.StepXI.contract-construction` | `StepXI/Contract.lean:64` | construct StepXIContract from IUT source data | `Mzk1StepXIMinimalStatementShaActual` (arithmetic skeleton), `Mzk1A763BoxAssemblyShaActual` (box coeff), `Mzk1StepXIFormalizationAttemptActual` | **PARTIAL** (contract is conditional; construction from source unfinished) |
| `IUT-III.source-column-carrier-identification` | `StepXI/FiniteSourceColumnTrunkBridge.lean:284` | API-9 second half: injective carrier/FPrimeStrip identification | `SourceColumnCarrierIdentification.lean` (landed trunk realization; pending = identification proper); our `Mzk1Cor312ChainCertificate` green assembly | **PARTIAL** |
| `IUT-III.source-adjacent-column-procession-isomorphism` | `StepXI/SourceAdjacentColumnProcessionIsomorphism.lean:324` | actual adjacent-column procession iso for (I,n) | file's landed components green; our `Mzk1HullLogVolumeFormulaActual`/scaled θ provide volume side | **PARTIAL** |
| `IUT-III.source-SHE-square-supply` | `StepXI/SourceSHETransportObligations.lean:397` | inhabitant of SHE square supply (sheSupply) | `SourceSHETransportLaws.lean`, `kummerMap_thetaOne`; `Mzk1KummerTransportActual` | **PARTIAL** |

**Verdict:** 0 of the 14 pending obligations is fully DISCHARGED by our green results.
11 are **PARTIAL** (green interfaces/conditional assemblies/volume side now exist; the
source-level construction or actual inhabitant is still missing), 3 are **MISSING**
(IUT-I source existence, the two alternative-route obligations; route-comparison audit
has only a markdown spec).  No pending status is stale in the sense of being actually
proved elsewhere; the a-priori statuses are conservative, not outdated.

## B. Our latest green results and where they attach

| our green | file (tmp/sheaf/xif/paper unless noted) | attaches to |
|---|---|---|
| S3137 q/θ readings | `S3137QThetaPilotLogVolumeReadingsActual` | P4/P5, volume side of IPL/SHE/APT |
| scaled θ-hull + iterated scaling law | `Mzk1ScaledThetaHullShaActual`, `Mzk1ScaledThetaHullScalingShaActual` | P7/sFactor, V_paper |
| normalized log +1 correction | `Mzk1ScaledThetaHullNormalizedLogShaActual` | volume dictionary |
| scaled paper 3.12 + VPaper | `Mzk1ScaledPaper312Actual`, `Mzk1VPaperActual`, `Mzk1ScaledClosingShaActual` | 3.11.5→3.12 volume side |
| h_V / explicit 3.12 | `Mzk1Paper312ExplicitActual`, `Mzk1Paper312FinalBoundActual`, `Mzk1Paper312ConditionsActual`, `Mzk1HVLemmaActual` | 3.11.5 checkpoint |
| c_V=1/4, σ*=6 | `Mzk1ShellCoeffComputationActual`, `Mzk1GapTightnessActual` | P7, box threshold |
| paper normalized Vol/Deficit | `Mzk1PaperNormMuActual`, `Mzk1PaperNormThetaActual`, `Mzk1PaperNormDeficitActual` | 3.11.5→3.12, A-cancellation |
| volume upper `V ≤ stepV` | `Mzk1VolumeUpperLeActual`, `Mzk1StepVIdentificationActual` | geometric box (OPEN) |
| Szpiro from box, `(1+eps)` | `Mzk1SzpiroFromBoxActual` | box → Szpiro (honest (1+eps)) |
| coefficient identities | `Mzk1A763BoxAssemblyShaActual`, `Mzk1BoxCoeffIdentificationShaActual` | P7/A763 bookkeeping |
| StepXI choice gap | `Mzk1StepXIFormalizationAttemptActual` | 3.11.5→3.12 missing lemma |
| StepXI arithmetic skeleton | `Mzk1StepXIMinimalStatementShaActual`, `Mzk1StepXISSIneqDictionaryShaActual` | contract construction |

## C. Still missing (precise)

1. **Actual source constructions** (not interfaces): `SourceLinkFactorization` inhabitant (IPL),
   `SourceAPTStatement` inhabitant (APT), SHE-square supply, adjacent-column procession iso,
   source-column carrier identification, `IUT-I.hodge-theater-source-existence`.
2. **Step-(xi) choice-existence proposition** `∃ κ ∈ κs, -A - κ ≤ V` (equivalently lana
   `WallOn`/`XiPrinciple` / SSIneq): the single open lower-bound input; P1–P5 do not imply it
   (lana `NonDerivable`), formalized as gap in `Mzk1StepXIFormalizationAttemptActual`.
3. **Geometric box** `V ≤ ((l+5)/4)·logdf + C0` and `V = stepVExpr` object dictionary
   (hull `Mzk1VolumeUpperLeActual`/`Mzk1StepVIdentificationActual` remain conditional).
4. **Volume identification with lana logVol** (archimedean, procession `1/nC`, c_lana) — §7.8.

## D. Files touched by this reconciliation

* this MD; * `tmp/sheaf/xif/paper/Mzk1StepXIReconciliationActual.lean` (machine table, EXIT=0, olean=True).
