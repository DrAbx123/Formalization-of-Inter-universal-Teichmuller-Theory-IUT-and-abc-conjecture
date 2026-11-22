# StepVIII input list (final ruling B, 2026-11-17) - sophie lane

Caliber: C2/C3/C4 unified on the paper-faithful v2 family; the legacy gamma
objects (actualQPilotMagnitudeClassical, p6SandwichChain M, actualThetaHullLogRoot)
are INTERIM/LEGACY only and must not enter the final consumption chain.

## Letters / objects

| slot | exact object | notes |
|---|---|---|
| Q | `Mzk1ULQPilotMagnitudeV2Actual.qPilotMagnitudePaper_v2` | paper Q_all = global normalized q-divisor degree (Def 1.9, 1/[F:Q], f_P weights); == (1/[Fmod:Q]) Sum ord_b logp via ord_P=e_P ord_b + Sum e f |
| M | `Mzk1ULQPilotMagnitudeV2Actual.M_paper_v2` | M = Q/(2l); paper |log q| = (1/2l) log q (IUT IV L1359-1364) |
| H_pkt weight | `thetaLamWeight` (kurt lambda weight; lambda=native local degree, lambda/d_mod) | paper Step(v) L1717-1718 lambda_e and L1860-1878 outer sum |
| theta | `ksThetaHullLogRoot` (K-side, M-scale) | needs the 2l-root hull-scaling datum (david 7b) for the M-scale identification |
| S_ar | `Mzk1ULPaperLettersActual.SAr_tripodal` | paper-faithful: log d_F (rootDiscr, 1/[F:Q]) + position-weighted log f_F (badFPrimeSet, david logConductorFActual) |
| d_mod | `Mzk1ULEModActual.eMod` (2l scaling side) / `Mzk1ULPaperLettersActual.dMod` | eMod for R4; dMod for d_mod |

## Open letter obligations entering the final chain

1. `hlogK_lambda` (david): paper Step (ii) with lambda weights, log d_K <= S_ar + 2 log l + 21;
   the +21 comes from the F vs F_tpd difference (paper L1412-1426).
2. `hsQ_lambda` (david): paper Step (iii) s^Q estimate with lambda weights;
   `sQPaper = prod_{p in V(Q)^dst} p` (distinct rational primes, IUT IV L1436-1501).
3. `hstepVIII_lambdaWeights` (kurt/david): the Step(viii) display with lambda/d_mod
   outer weights, i.e. Sum_b lambda_b/d_mod * B_b <= kappa*((1+12 d_mod/l)*S_ar + 2 log l + 56
   - cL(l)*Q + (20/3)*paperLstarLogs) - M with Q=v2, M=M_paper_v2.
4. `hprime` (andrew): the prime-counting/Section2 donor for the arch and +2log l pieces.
5. `D2SecondForm` (this lane): the D2 second display for h=Q_all vs the selected Q; the
   h - Q decomposition uses david's QSelected (per-prime relation; no cross-fibre choice).
6. `QSelected` (david): route 6.2 selected q magnitude (f_P weights on the selected lifts),
   audited alongside v2; the connection equality to v2 is the still-open interface.

## Updates (hcond chain / D4 bridge / D4Inputs)

- hcond: `Mzk1ULHcondChainActual` (david, DONE 00:48:16) provides
  `LegendreTpdSupport` (logFtpd/logPointND/log2Const + perPlace_bound + log2Const_le),
  `hcond_after_absorb : logFtpd <= logPointND + Real.log 2`, `LegendreSupportIncl`
  (qSupport/tpdBadPrimes/pointBadPrimes + tpd_subset/q_subset_point) and
  `tpd_subset_point_of`.  Our `Mzk1ULHcondSkeletonActual` packages
  `HcondStatement` (pointND form) and the assembly `tripodalDictionary_of_hcond`;
  filling it needs david's Legendre equality + the per-place f_P/[F:Q] alignment.
- D4 bridge: `Mzk1G1D4BridgeActual.d4_of_c4_qscale` (andrew, 00:43:15, v2 caliber
  Q=h) / `d4_absorption`; our `Mzk1ULD4InputsActual` (00:46:08) supplies
  Q_eq/M_eq/S_ar_eq/d2 for that consumption once the v2 hstepVIII is proved.
- QSelected: `Mzk1ULQSelectedConsumersActual` (00:42:16) records M = Q/(2l) and the
  Q/M slot relation parametrically (MOfQ/HstepVIIIQM).

## L-H consumption (andrew's D1LetterSource, 2026-11-17 12:20)

`Mzk1G1D1LettersActual.d1AnalyticInput_of_letters (L : D1LetterSource D d)`
reduces `D1AnalyticInput` to the per-lambda `D1LetterSource`; its `hlarge` needs:
- hC4 (v2 C4, Q=h): the v2 hstepVIII (this file's `hstepVIII_lambdaWeights`) +
  hP5 (`-M_paper_v2 <= ksThetaHullLogRoot`, kurt), consumed by
  `Mzk1UCHthetaWiringKSideActual.uc_c4_of_hthetaKSide`;
- hlup/hlog: `Mzk1ULD2SecondFormActual.D2SecondForm` (our `D4Inputs.d2`);
- hSD: `S_ar = SAr_tripodal` (`D4Inputs.S_ar_eq`);
- Q/M: `D4Inputs.Q_eq` (v2), `M_eq` (M_paper_v2);
- hlogK/hsQ: our `D4Inputs.hlogK`/`hsQ` (explicit obligations; david's lambda versions
  replace them once proved).

## Consumption shape currently in Lean

- `Mzk1UCHthetaWiringKSideActual.C2ThetaInputK` + `uc_c4_of_hthetaKSide`: M := MpaperV2,
  theta := ksThetaHullLogRoot, hThetaUpper := kurt ksThetaHullLogRoot_le_ucWeightedHpkt
  with weight normDegreeWeight (to be switched to lambda/d_mod), hstepVIII is a caller
  argument (must use lambda/d_mod LHS per ruling B).
- `Mzk1ULD4InputsActual.D4Inputs` (frozen numbers, docstrings only): Q = v2, M = M_paper_v2,
  S_ar = SAr_tripodal, hlogK/hsQ = the actual-letter obligations above, d2 : D2SecondForm.
- `Mzk1ULD2SecondFormActual.D2SecondForm`: statement shape of the D2 second display.
- `Mzk1ULD2V2SkeletonActual`: hAllV2 := v2; QSingle := legacy qPilotMagnitudePaper (reference
  only); PerPrimeLiftData / PrimeCutoffData intermediate interfaces.
