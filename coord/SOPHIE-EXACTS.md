# sophie lane exact names (handoff, updated 2026-11-17 12:15)

All files compiled DONE via watchdog (three axioms) unless marked otherwise.

## Paper letters / D-slot

- `Mzk1ULPaperLettersActual`: `dMod`, `one_le_dMod`, `logDifferentF`, `one_le_rootDiscr`,
  `zero_le_logDifferentF`, `logConductorF`, `zero_le_logConductorF`, `SAr`, `zero_le_SAr`,
  `logDifferentK`, `zero_le_logDifferentK`, `SAr_K`, `zero_le_SAr_K`,
  `SAr_tripodal` (paper-faithful: logDifferentF F + Mzk1ULBadFPrimeSetActual.logConductorFActual),
  `zero_le_SAr_tripodal`.
- `Mzk1ULPaperWeightActual` (auxiliary): baseLambda/pFiber/localTotal/paperWeight + proofs
  (paperWeight is the Step(v) inner lambda/localTotal slot only).
- `Mzk1ULEModActual`: `ramificationIdxOverInt`, `eMod (T) = sup ... ⊔ 1`, `dModFmod`,
  `one_le_eMod`, `eMod_le_finrank`, `eMod_le_dMod`, `dModFmod_pos`.

## K-side letters (hstepVIII chain)

- `Mzk1ULKSideLettersActual`: `ksP`, `ksPlace`, `ksD`, `ksLogP`, `normDegreeWeight`,
  `ksP_eq_qVFamTensorP`.
- `Mzk1ULSideWeightBridgeActual`: `RamifiedBad`, `ramifiedBad`, `mem_ramifiedBad_iff`,
  `badPlaceSet`, `badPlaceSet_subset_differentPlaces`, `ksD_eq_paperOrder_mul_ksLogP`.
- `Mzk1ULTripodalFieldActual`: `jOfLam`, `FmodLam`, `FtpdLam`, `FLam`.
- `Mzk1ULTripodalFieldMembersActual`: `FmodLam_eq_adjoin`, `FtpdLam_eq_adjoin`,
  `jOfLam_mem_FtpdLam`, `lam_mem_FtpdLam`, `FmodLam_le_FtpdLam`.

## TripodalDictionary / hcond

- `Mzk1ULTripodalDictionaryActual`: `logDiff`, `dFtpd`, `fFtpd`,
  `logDiff_eq`, `dFtpd_pos`, `fFtpd_pos`,
  `tripodalDictionaryOfConductor` (hcond : pointND form).
- `Mzk1ULHcondSkeletonActual`: `HcondStatement`, `hcondStatement_iff`,
  `tripodalDictionary_of_hcond`.

## C2/C4 (theta side, MpaperV2 wiring)

- `Mzk1UCHthetaWiringKSideActual`: `MpaperV2`, `C2ThetaInputK`, `c2ThetaInputK_of_hperB`,
  `uc_c4_of_hthetaKSide` (M = MpaperV2; hstepVIII caller argument; ruling B).

## D2 / D4 / QSelected

- `Mzk1ULD2SecondFormActual`: `D2SecondForm`, `D2SecondForm.Q_le_h`,
  `D2SecondForm.second_form`, `D2SecondForm.second_form'`.
- `Mzk1ULD2V2SkeletonActual`: `hAllV2`, `hAllV2_eq`, `hAllV2_nonneg`, `QSingle`,
  `PerPrimeLiftData`, `PrimeCutoffData`, `d2SecondForm_of_data` (interfaces only).
- `Mzk1ULD4InputsActual`: `D4Inputs` (Q = v2, M = Mpaper_v2, S_ar = SAr_tripodal,
  hlogK, hsQ, d2), `D4Inputs.Q_is_v2`, `M_is_MpaperV2`, `S_ar_is_tripodal`.
- `Mzk1ULQSelectedConsumersActual`: `MOfQ`, `MOfQ_eq`, `HstepVIIIQM`,
  `HstepVIIIQM.elim`, `HstepVIIIQM.unique`.
- `Mzk1ULStepVIIIInterfacesActual`: `hlogK_lambda`, `hsQ_lambda`,
  `hstepVIII_lambdaWeights` (Prop shapes, ruling B).
- `Mzk1ULSQPaperActual`: `qSupportPrimes`, `dSupportPrimes`, `specialPrimes`, `sQPaper`,
  `log_prod_natCast_eq_sum`, `log_sQPaper_eq_sum_log`, `specialPrimes_ne_zero`.
- `Mzk1ULBadFPrimeSetNeBotActual`: DOCUMENTED TODO file (superseded by the closure below).
- `Mzk1ULSQPositivity2Actual` DONE 10:12:45: **`badFPrimeSet_ne_bot`** PROVED
  (`IsDedekindDomain.mem_primesOverFinset_iff hp B` + `Ideal.ne_bot_of_mem_primesOver`).
- `Mzk1ULSQPositivity3Actual` DONE 10:24:54: **`qSupportPrimes_ne_zero`**,
  **`dSupportPrimes_ne_zero`** PROVED (differentPlaces via `primeFactors`/
  `mem_primeFactors` + `mem_normalizedFactors_iff` + differentIdeal != 0).
- `Mzk1ULSQPaperFinalActual` DONE 10:29:11: **`log_sQPaper_eq_sum_log_paper`**,
  the UNCONDITIONAL paper identity log(s^Q) = Sum_{p in V(Q)^dst} log p
  (IUT IV L1436-1501), hq/hd discharged.
- `Mzk1ULSQPaperUncondActual`: re-export with explicit hq/hd (kept for reference).

## D4Inputs <-> D1LetterSource (andrew's L-H assembly, 2026-11-17 12:20)

`Mzk1G1D1LettersActual.D1LetterSource (D) (d)` per-lambda `hlarge` fields map to
`Mzk1ULD4InputsActual.D4Inputs (T)` as follows:

| D1LetterSource.hlarge | D4Inputs source |
|---|---|
| hSD (tripodal S_ar) | `S_ar`, `S_ar_eq : S_ar = SAr_tripodal` |
| hlup / hlog (D2) | `d2 : D2SecondForm` (`h_sub_Q_nonneg`, `h_sub_Q_le`; see also `Mzk1ULD2SecondFormCorollariesActual.Q_le_h'`, `.h_eq`) |
| hC4 (v2 C4, Q=h) | open: v2 hstepVIII (lambda weights) + hP5 (`-M_paper_v2 <= ksThetaHullLogRoot`) via `Mzk1UCHthetaWiringKSideActual.uc_c4_of_hthetaKSide` once the lambda-weight C3 is proved |
| Q/M in andrew's `d4_of_c4_qscale` | `Q_eq : Q = qPilotMagnitudePaper_v2`, `M_eq : M = M_paper_v2` |
| hlogK/hsQ (still obligations) | `D4Inputs.hlogK`, `D4Inputs.hsQ` (explicit; wait for david lambda versions) |

## hcond (TripodalDictionary inhabitant) - remaining fill

- Target: `Mzk1ULHcondSkeletonActual.HcondStatement` (pointND form), assembled by
  `tripodalDictionary_of_hcond` into `G1D2InterfaceActual.TripodalDictionary`.
- david gives `Mzk1ULHcondChainActual.LegendreTpdSupport.perPlace_bound`
  (`logFtpd <= logPointND + log2Const`) and `hcond_after_absorb`; the remaining
  work is the per-place f_P/[F:Q] alignment of our `logConductorFActual` sum with
  `logFtpd` and `pointND` (same domain: F_tpd = Q(lambda) by the Legendre ruling).
- Support inclusion: `LegendreSupportIncl` (`tpdSubset`, `qSubset`) +
  `tpd_subset_point_of`; the log 2 constant is absorbed into the C2 hP5 constant.

## Legendre / tripodal bridge (sophie, DONE 11:29:35)

- `Mzk1ULLegendreTripodalEqActual` (imports david's `Mzk1ULLegendreTwoTorsionActual`,
  `Mzk1ULTripodalConductorActual`, `Mzk1ULTripodalFieldActual/Members`, Legendre curve API):
  - `legendre_nonsingular_zero (h0) : Nonsingular 0 0`; `legendre_nonsingular_one (h1)`;
    `legendre_nonsingular_lam (h0) (h1)`;
  - **`twoTorsionXOf_legendre (lam) [IsElliptic] (htwo) (h0) (h1) :
    twoTorsionXOf ℂ (legendreWeierstrassCurve lam) = {0,1,lam}**;
  - **`legendre_tripodalAdjoin … :
    adjoin ℚ (insert E.j (twoTorsionXOf ℂ E)) = adjoin ℚ {jOfLam lam, lam}**
    (stated over ℂ since david's `tripodalFieldOf` requires `[NumberField F]`;
    docstring records the transport caveat);
  - **`legendre_tripodalAdjoin_eq_FtpdLam … : … = FtpdLam lam`**.
- Consumer note: `Mzk1ULHcondChainActual.LegendreTpdSupport` is purely numeric
  (logFtpd/logPointND/log2Const + perPlace_bound/log2Const_le), so this bridge
  supplies the DOMAIN identification only; the numeric per-place alignment
  (f_P/[Q(lam):Q]) and the place-weighted `fFtpd` remain the open hcond content
  (caliber question raised to Lead: keep prime-counted logConductorF (NOT-PAPER)
  or switch TripodalDictionary.fFtpd to a place-weighted conductor).

## F3 (H-T)

- `Mzk1HTF3ConductorHeightActual`: `TruncatedConductorHeightData`,
  `truncatedConductorHeight_le_height_add_const`.

## Docs written

- `coord/C2-CALIBER-AUDIT.md` (C2 caliber: gamma vs f, 1/(2l) column, addendum Mpaper_v2 Fmod form)
- `coord/Q-NORMALIZATION-AUDIT.md` (v2 1/[F:Q] vs StepV 1/[K_w:Q_p]; c_norm=order/e)
- `coord/STEPVIII-INPUTS.md` (ruling B input list + hcond/D4 updates)
- this file
