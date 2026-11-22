# NODE STATUS — 2026-11-17 01:40 (Lead dashboard)

Authoritative route: `coord/P7-G1-P6-P8-CLOSURE-ROUTE-20261116.md`.
Gate: `tools/wd_gate.mjs` (watchdog only; whitelist `dag/watchdog/extra-targets.txt`).
Snapshot: gate total 202 / DONE 193 / FAIL 4 / STALE 4 / NO-OLEAN 3 / forbidden tokens 0.
This file is a **status summary**, not evidence: each item points to watchdog DONE files / audit verdicts.
Closure requires route §9.1 exits + audit batch verdict; "CLOSED" below means the named theorem
is DONE (three axioms) and audited, not that the route node's contract is fully discharged.

## G-A — Fermat curve Y_n / P¹ / π / smooth-proper
DONE (canonical models):
- canonical Y_n glue `Mzk1HullFermatGluingActual` 13:37, `Mzk1G1FermatTwoChartGluingActual` 12:48, `Mzk1G1FermatCurveActual` 00:07; P¹ glued `Mzk1G1ProjectiveLineGluedActual` 00:31 (+transition 00:43, PiOverlap 12:44, ChartPreimage 16:26, M-a bridge `overlapToChartInf_opensRange_eq_composite` 16:36).
- π `Mzk1G1FermatPiActual` 13:19; preimage decomposition `Mzk1G1FermatPiPreimageActual` 13:31.
- π⁻¹ chart equalities **CLOSED**: `Mzk1G1FermatPiPreimageCloseActual.pi_preimage_localChart0` 16:44:16 + `Mzk1G1FermatPiPreimageClose2Actual.pi_preimage_localChartInf` 16:50:10 (both DONE, 0 sorryAx).
- structure morphism `Mzk1G1FermatCurveToSpecActual` 14:00 (`fermatCurveToSpec`, ι0/ι1).
- chart finiteness `Mzk1G1FermatChartFiniteActual` 13:48 / ChartFinite2 13:53.
- **IsFinite π CLOSED**: henry `Mzk1G1FermatPiRestrictFiniteActual.isFinite_pi` 17:16:42; grace independent `Mzk1G1FermatPiFiniteChartActual` 17:17:53.
- **IsProper(Y_n) CLOSED**: grace `Mzk1G1FermatPiProperActual.fermatCurveToSpec_isProper_final` 17:19:19 (uses grace `_cond` 15:55 + henry isFinite_pi + alan `p1GluedToBase_isProper` 15:53).
- chart-level smooth rel dim 1 DONE: λ-chart `Mzk1G1FermatCurveSmoothActual.chartSpec_smoothOfRelativeDimension` 15:55:41; ∞-chart `Mzk1G1FermatCurveSmooth2Actual.chartSpec2_smoothOfRelativeDimension` 16:42:12.
- **glued smooth CLOSED**: grace `Mzk1G1FermatCurveSmoothFinalActual.fermatCurveToSpec_smoothOfRelativeDimension` 17:40:31 (uses Lead `chartOpenFamily` cover + chart restrictions; three axioms).
IN FLIGHT:
- (h) geometric integrality/connectedness of Y_n⊗k̄: grace started (chart-level k̄ base change → overlap nonempty → glued integral via `chartOpenFamily_iSup_eq_top`; plan approved by Lead).

## G-B — Kähler differentials / Ω ≅ O(n−3) / ramification
DONE: Ω `Mzk1G1OmegaActual`, Basis, Free, TransitionGlobal (A3) 14:44, Infinity 14:59, InfFree 15:23, LineBundle (A5 transition units + π pullbacks) 16:08, LineBundleData (`boundaryRamificationAlgebraData` + three named interfaces) 16:13/16:38, RamificationLocal 16:25 (λ=0,1 e=n), RamificationInfinity 16:36 (**∞ e=n, arbitrary K/ζ**).
=> boundary e=n all three fibers PROVEN (three named theorems).
REMAINING (audit-deferred): Ω explicit quotient presentation; divisor-layer A5 full iso; scheme-level sheaf objects (§9.2); §3.3 three different named interfaces (NO INHABITANT).

## G-C — global Belyi/noncritical ψ, B1/B2/B3
DONE: GlueMorphism 12:59, PsiXi 13:13, PsiAffineOverlap 13:45, B1① PsiProductIdentity 13:51, B1② PsiAffineCompat 14:11, B1③ `Mzk1G1PsiCoverActual.psiOpenCover` 16:38:46, HY-a `Mzk1GlueCocycleActual` 16:53:40, HY `Mzk1G1PsiGlobalActual.overlapToCurve_condition` 17:00:24, hcomp right leg `Mzk1G1PsiHcompRightActual.hcomp_right_eq` 17:30:23, psiChart0/1 16:50:10.
IN FLIGHT: B1④ hcomp main assembly (emmy L0 + henry right leg; `Mzk1G1PsiGlobalActual` FAIL 17:32 iterating); then ⑤ ψ glueMorphisms, ⑥ finite-beta h + `b1FiniteProducer`; B2 scheme ψ; B3 φ*O(1)≅L^⊗d, ω_Y(E_φ)≅φ*ω_P¹ (waits G-B).

## U-R — C2 q/θ dictionary
DONE: RootMass/RootExtension/RootExtInstances, ThetaHull, ThetaRegion, QNormalization (M=Q/2l), ThetaMonotone, ThetaPacketCarrier, ThetaTransport, ThetaHtheta (`ur_htheta_of_scaling`), ThetaHullUpper (`padicFractionalLattice_eq_intCeil`), CollectionLayer 16:20, SmallPrime (`ur_badWeightedLogP_le`) 16:35, BadWeightSum 16:32, ThetaHullTensor stage1 17:32 (`congruence`, `urCeilCoeff`, `urLocal_ball_eq_ceil`), ThetaHullGeneric 17:27 (generic hull lemmas).
IN FLIGHT: θ=0 concrete corollary vs whnf/heartbeat — approved (i) `urThetaFamily` abbrev then fallback (iii) generic+nz defs only (θ=0 = audit semantic observation, NOT htheta evidence); `urNonzeroLabel*` defs; then label-1 ball bound → per-b packetB → **htheta(nz)**.
DECISION (Lead 2026-11-17): (a) accept θ=0 语义 for C2 **REJECTED** (zero-collapse ban); (b) modify actualRootThetaImageSet **NOT approved** (audit); (c) coexist: actual θ=0 honest observation + `urNonzeroLabelHull` route object. (ii) root-extension StepV bound on L PROJECT approved (kurt, 2–3 batches) as the only path to remove retained hVh.

## U-L — Step(viii)/paper constants
DONE: Hpkt/StepVIII (`Mzk1ULStepVIIIActual` 16:58:56: `hstepVIII_of_collectionLayer` uses david `hviTable_final`+`hviTable_instance`; trivial nonneg internal; hvii provable; **retained = hX + hiii**), WeightedHull, StepVWeights, StepVIIIActual (aggregate letters + `logP_aggregate_le_logSQ` proven), HviTableActual, HviTableLetters, HviTableFinal (`hviTable_final`) 16:35:55, HviTableInstance (`hulllog_le_collectionBound_of_paperBound` 17:01, `hVh_of_paperBound_letters` 17:09, `labelDifferentSum_nonneg` 17:16, `hVh_of_labelData` 17:33:43), StepVHullPaper (`hV_of_L814_data` 17:24:40), HviTableBridge, StepVDisplayIdentity.
NOTE: (A) hVh now a general conditional theorem `hVh_of_labelData D`; C4 condition = LabelStepVHullData family (varpi existence = S342/UR retained; hpaper provenance = accepted L814). T-side concrete instantiation deferred to sophie (qVFam expansion).

## U-C — C3/C4 assembly
DONE: UCHpkt 14:29 (C3/C4 paper constants of P6), ThetaHullControl2 15:05, UCC1Upper, UCLWeights, UCC3Producer, QReadingNegM, UCHthetaWiring (`htheta_of_hperB`/`uc_c4_of_htheta`, HthetaInput slot PENDING).
C4 CONDITIONS (current): **htheta (kurt nz version) + hiii + hX + LabelStepVHullData family** (hviTable/hvii/trivial nonneg/hVh-arbitrary removed).

## L-H — D1 actual criterion + D3
DONE: KvCompact, LocalHeightCriterion, D1Producer, QHeight upper (13:18), JHeightBezout 13:29, JHeightLower 13:59, JHeightD3Actual 15:57 (`jHeight_relation` per-K), D2Interface (NO INHABITANT) 16:02, JHeightUniformProbe 16:16, JHeightUniform step1 16:55 (`coeffAbsSum` family).
IN FLIGHT: step2 (`support_card_le`, `coeffAbsSum_mul_le` — method A approved) → step3 coeff_map → step4 mulHeightBound → step5 `jHeight_relation_deg : ∀d ∃B_d` (uniform D3, route §6.3 NEW). Then D1AnalyticInput + (d) (impact report first), D4 after U-C.

## G-K / L_p
DONE: FiniteDisjointBelyi 13:11, DisjointFamily 13:13 (`B1FiniteProducer`, `b1StepProducer_of_finite`, `hasGluedBelyiFamily_of_b1`, GKC inputs), LpFiniteness 13:21, LpDifferentBound 13:30, LpHenselNearRoot 14:12.
IN FLIGHT: B1 global φ_i (emmy ⑤/B1), `BoundedDegreeFinitelyManyFields` true proof (kurt), X=∏Y_n(L_v)^d compactness (after IsProper Y_n — now available).

## H-T / F7 / F1–F8 (biggest route gap)
DONE: F7 interface (`Mzk1G1FermatRadicalSupportActual.f7_normalizedLogDisc_le_of_div_ramification` 14:31), `RadicalSupportFinal3` (residue_separable_global) 14:03, `Mzk1F7TameCountGlobalActual` 14:07, §8.1 interface `Mzk1HT81InterfaceActual` 16:56 (+HT81LineBundleHeights 17:22).
CONDITIONAL: F7 (i) p∤abc⇒unramified, (iii) p|n constant, hdiv/htame — actual Fermat-lift number field K missing upstream.
§8.2 conductor/different: alan batch1 `Mzk1G1ConductorDifferentCancellationActual` 16:50 (`F2`/`F3` named + tower formula), batch2 `...CoreActual` 17:10 (conductorDifference ≤ differentTerm + tower log identities); batch3 in flight (place-sum instantiation; `differentTerm ≤ log|N(diff)|/[L:Q]` NEW, conditional `hdifferentNorm` provenance).
§8.3/§8.4/§8.5/§8.6 + F1–F8 height transport: NOT started.

## P8-P — (F) producer / ABC
DONE: `Mzk1P8EpsilonSelectionActual`, `Mzk1P8FreyAssemblyActual` (`freyJProductHeightCriterion_of_logConjecture`, `abcConjecture_of_logConjecture`), F7 disc chain.
TODO: P8-P producer = H-T F1–F8 + L-H D1 + G-K outputs ⇒ F9 log bound; current files conditional by design (no fake producer).

## Compliance discipline (enforced)
- Only watchdog compiles; no lake env lean.
- Gate forbidden tokens = 0 in every check; no literal sorry/axiom/PUnit/True/toy in whitelist.
- "File DONE ≠ contract theorem exists": grep + axioms before citing; stale-olean/content-mtime checks in audit19.
- Retained paper intermediates must be named structures with exact citation, marked no inhabitant; never axioms; zero-collapse (θ=0 for C2) banned.
- xi ≠ pi; Y_n model must be named in citations; TauCetiPort closed (don't import).
- Scratch/probe files must not be whitelisted.
