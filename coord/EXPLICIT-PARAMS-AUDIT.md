# Explicit-parameter audit (all lanes, sophie's read) - 2026-11-17 18:00

Rule: every explicit h parameter / conditional interface below is a PENDING
obligation, NOT a closed node and NOT counted as progress.  For each we record the
equivalent unproved object, owner, and the concrete construction plan.

## A. C2/C3/C4 chain (theta / hstepVIII / hP5)

| h parameter | equivalent unproved object | owner | plan |
|---|---|---|---|
| `hP5 : -M_paper_v2 <= ksThetaHullLogRoot` | J1: local Kummer mass `(1/2l) log|q| = log|r|` + region inclusion, at M scale | kurt | 7b: 2l-root hull scaling datum (`q^{c/(2l)}`) + J1 mass formula + possible-images region |
| `hstepVIII_lambdaWeights` | paper Step(viii) display with lambda/d_mod outer weights, Q = v2, M = M_paper_v2 | kurt (+david per-prime) | rebuild F-side hull/collectionBound with lambda weights (`Ideal.sum_ramification_inertia`, `fiber_sum_ef`), then per-b alignment to v2 |
| `htheta : theta <= ucWeightedHpkt w V` | K-side StepV hull bound with lambda weights (currently normDegreeWeight) | kurt | `ksThetaHullLogRoot_le_ucWeightedHpkt` lambda-weight version |
| `hC4` (andrew's D1LetterSource.hlarge) | v2 C4 `cL l Q <= paperA` | andrew + sophie | `uc_c4_of_hthetaKSide` once hP5/hstepVIII above are proved (no new condition) |

## B. Paper Step (ii)/(iii) letters

| h parameter | equivalent unproved object | owner | plan |
|---|---|---|---|
| `hlogK_lambda` (Mzk1ULStepVIIIInterfacesActual) | paper L1412-1426: log d_K <= S_ar + 2 log l + 21 with paper letters | david | `log_rootDiscr_eq_add` tower identity + wild bound (`Mzk1ULSerreWildBoundActual` count lemmas) + absolute conductor per-place + R1 constants |
| `hsQ_lambda` | paper L1553-1575: log s^Q <= 2 d_mod S_ar + 5 + log l | david | sQPaper primorial (`Mzk1ULSQPaperActual`) + absolute conductor per-place + Prop 1.3(i) support + numeric log(2*3*5*l) |
| `hsQ` field inside D4Inputs | same as hsQ_lambda | david | same |
| `hlogK` field inside D4Inputs | same as hlogK_lambda | david | same |

## C. TripodalDictionary / hcond

| h parameter | equivalent unproved object | owner | plan |
|---|---|---|---|
| `fFtpd_le_conductor` (= `HcondStatement`) | paper L617-621: log f_Ftpd <= N_D(lambda), pointND on the point field | david (Legendre) + sophie (assembly) | Legendre 4 declarations (`twoTorsionXOf_legendre`, `tripodalFieldOf_legendre_eq_adjoin`, `= FtpdLam`) + `LegendreTpdSupport.perPlace_bound` with f_P/[F:Q] alignment + `LegendreSupportIncl` support inclusion; log 2 absorbed into C2 constants |
| `dmod : d` in TripodalDictionary | D1 degree-bound convention ([Fmod:Q] <= d) | sophie | document only; actual per-lambda degree needs T, not available at the generic dictionary |
| `eStar`/`Cd` | R4 constant control | sophie/david | supplied at T wrapper; `eStarMod` composite constant (david 19:16 check) |

## D. D2 / D4 / QSelected

| h parameter | equivalent unproved object | owner | plan |
|---|---|---|---|
| `D2SecondForm` (d2 in D4Inputs) | h = Q_all vs selected Q: per-prime lift multiplicity + C_d sqrt h log(2 C_d h) + C_KV | david (QSelected/OrdTower) + Section2 | david `Mzk1ULQSelectedActual`/`Mzk1ULOrdTowerActual` (`ord_P = e_P ord_b`, `MpaperB_eq_ordB`) + `PrimeCutoffData` from Section2/Chebyshev |
| `PerPrimeLiftData` | `hMinusQ = v2 - QSelected` decomposition and nonnegativity | david | from `qPilotMagnitudePaper_v2_eq_sum_Qb`/`MpaperB` and the selected sub-sum |
| `PrimeCutoffData` | C_d sqrt h log(2 C_d h) + C_KV cutoff estimate | Section2/andrew | Chebyshev/prime-count donors |
| `QSelected` connection to v2 | equality/inequality of selected sum vs full-fiber sum | david | per-prime ord tower (`ord_P = e_P ord_b`), still-open interface |

## E. sQ support positivity - CLOSED 2026-11-17 (real closure, not conditional)

`Mzk1ULSQPositivity2Actual.badFPrimeSet_ne_bot` (10:12:45),
`Mzk1ULSQPositivity3Actual.qSupportPrimes_ne_zero`/`dSupportPrimes_ne_zero` (10:24:54),
`Mzk1ULSQPaperFinalActual.log_sQPaper_eq_sum_log_paper` (10:29:11): the paper
primorial identity log(s^Q) = Sum_{p in V(Q)^dst} log p (IUT IV L1436-1501) is now
proved unconditionally (support positivity discharged via
`IsDedekindDomain.mem_primesOverFinset_iff`+`Ideal.ne_bot_of_mem_primesOver` and
`primeFactors`/`normalizedFactors`+differentIdeal != 0).  The entries below are
historical (the obligation is closed).

### historical entries

| h parameter | equivalent unproved object | owner | plan |
|---|---|---|---|
| `hq : qSupportPrimes nonzero` | P in badFPrimeSet => P != bot | sophie | `mem_primesOverFinset_iff` (deprecated root alias vs namespace) + `Ideal.ne_bot_of_mem_primesOver` |
| `hd : dSupportPrimes nonzero` | P in differentPlaces => P != bot | sophie | `Ideal.mem_normalizedFactors_iff` + `Ideal.differentIdeal_ne_bot` |

## Status of related DONE anchors (not obligations)

- `Mzk1ULSQPaperUncondActual` DONE 04:22:40 (with hq/hd explicit per E).
- `Mzk1ULBadFPrimeSetNeBotActual` DONE 04:04:50: documented TODO only.
- `Mzk1ULHcondSkeletonActual` 01:03:03 (`HcondStatement`, `tripodalDictionary_of_hcond`).
- `Mzk1ULTripodalDictionaryActual` 00:57:26 (pointND form).
- `Mzk1ULD4InputsActual` 00:46:08; `Mzk1ULStepVIIIInterfacesActual` 00:28:55.
- `Mzk1ULD2SecondFormActual` 23:57:07; `Mzk1ULD2SecondFormCorollariesActual` 04:18:04.

## hbad dNo 段（paper L1555-1572 / Prop1.3(i) local support）——具名 obligation（2026-11-17, Lead 裁 (i)+(ii)）

- **义务**: dNo 的求和界（Ftpd 的 different support 扣 special），不可用 per-p 系数：单分歧位 e=2,f=1 时系数 2/[Ftpd:Fmod]=1/3<1（Lead 反例）。
- **paper**: IUT IV L1555-1562（per-place local 界）、L1461-1501（sF*_vQ/deg 定义）、L1572（global 2d_mod）。
- **owner**: david（local 对象+求和恒等）+ emmy（localization 层）。
- **消去计划**: Mzk1ULHbadLocalActual 的 s_vQ/d_vQ/f_vQ 定义与 Prop1.3(i) 局部界 → 求和恒等 → 消去 hbad 的 hd 参数。
- **状态**: 未闭合；hbad final 以 hq/hd 显式参数存在（不 fake、不计闭合）；qNo 段（unramified bad p）可先真证。
- **辅助**: Mzk1ULHbadSegmentsActual.{perPrime_unramified,perPrime_ramified} 纯算术，仅辅助。

## hlocal 的 paper input（2026-11-17 Lead 澄清后）

- **唯一剩余具名义务**: `(obligation: prop18_support_classification)` —— D0/D6/Prop1.8(vi)(vii): p∉{2,3,5,l} 时 s_vQ 的支撑元素分类（q-支撑 => conductor 局部系数覆盖 s 项；d-支撑 => 与 unramified 矛盾）。owner: grace+sophie（λ 实例化）。
- 不登记 `e_eq_one_away_special`（Lead 澄清: 直接 by_cases e_v：e_v≥2 ⇒ ramified（δ_abs≥e_v−1 ⇒ e_v≤2δ_abs）；e_v=1 ⇒ unramified-at-Q（δ_abs=0，donor `differentExponent_eq_zero_of_unramified`））。
- 算术分支已闭: `Mzk1ULHbadHlocalActual.e_le_two_mul_delta`、`Mzk1ULHbadHlocalBranchActual.ramified_branch/unramified_branch`、`Mzk1ULHbadHlocalCasesActual.hlocal_by_cases`。

## hspecial donor 切换（2026-11-17 Lead）

- **采用**: `Mzk1ULSpecialPrimesOwnActual.{log_two_three_five_le_five, specialPrimes_log_sum_le_own (l : PrimeGeFive) : Σ_{p∈specialPrimes l} log p ≤ 5 + log l}`（DONE 14:42:07，三公理）。
- **作废**: `Mzk1ULSpecialPrimesNumericActual`（probe 检查有 sorryAx + olean 缺失）、`_ProbeSpecialAxActual`、`Mzk1ULHbadAssemblyActual`（Lead 已从 watchdog 白名单剪除，见 `coord/watchdog-pruned-targets-20261119.txt`）。
- **闭合件**: `Mzk1ULHsQTruncClosedActual.hsQ_lambda_numeric_trunc_closed (hbad') : log sQ ≤ 2 dmod S_ar + 5 + log l`（hspecial 槽已由 own 件填）。

## R2 口径（2026-11-18 Lead 新路线）

- **hsQ**: 必须用 **actual finite bad-prime support 的 log-product**（V(Q)^dst 的实际素数集），**不是** `urSQ(max bad prime)` 的放大版；q-support（bad moduli）、different-support、special（2,3,5,l）三段分开记录，不再走 primorial 放大路线（旧 urSQ 路线 retired）。
- **hlogdK**: 按 K/Ftpd 塔分 good/tame/wild：good（p∤2·3·5·l，unramified）用 `differentExponent_eq_zero_of_unramified`/`delta_eq_zero_of_ramificationIdx_eq_one`；tame 用 Prop1.3(i) 下界/上界；wild 用 Prop1.3(ii)（`iutIVProp13ii_normalizedDifferent_le_zLocalization`）+ Serre wild 件；discriminant tower 经 `log_rootDiscr_eq_add` 得 `S_ar + 2·log l + 21`（21 = F vs Ftpd 层差，paper L1414-1416，已证非义务）。
- **S_ar 域**: F 层（或 Ftpd 层），F vs Ftpd ≤21 由 paper L1411-1425 明文；不再用 Fmod 层。
- **hsQ 常数**: `2·d_mod·SAr + 5 + log l`（paper L1572），hspecial 由 `Mzk1ULSpecialPrimesOwnActual.specialPrimes_log_sum_le_own`（DONE 14:42:07）填；旧 SpecialPrimesNumeric 作废。

## R2 hsQ 口径溯源（sophie 核，2026-11-18）

- `Mzk1ULR2HsQSupportActual.hsQ_actualSupport` = `Mzk1ULSQPaperFinalActual.log_sQPaper_eq_sum_log_paper`（IV L1436-1501 distinct-primes primorial, e_v=1）；
- `hsQ_actualSupport_split` = `log_sQPaper_eq_trunc_add`（(D2) 三段拆分）；
- `hsQ_actualSupport_bound`：形状与 IV L1572 `2d_mod(...)+log(2·3·5·l) ≤ ...+5+log l` 一致；hspecial 由 `Mzk1ULSpecialPrimesOwnActual.specialPrimes_log_sum_le_own`（无 sorry）闭合；`hbad'` 显式 = dNo 具名义务链；
- S_ar 用 F 层 `SAr_tripodal`；F vs Ftpd 差 ≤21 按 paper **L1411-1425**，由下游 56 常数吸收（docstring 溯源补记此处）。

## R2 hlogdK 溯源（sophie 核，2026-11-18）

- `Mzk1ULR2HlogdKTowerActual.hlogdK_tower` = `Mzk1G1HlogKAssemblyActual.hlogK_of_relative_different_bound`（相对 different 上界 `hbound` 显式输入）再 +21 slack；
- `SAr_F = logDifferentF (T.arithmetic.F) + logConductorFActual T`（= `Mzk1ULHbadFLevelActual.SAr_F`）；
- +21 对齐 paper IV L1414-1425（F vs Ftpd），**不吸收 h 槽 [F:Q]**；
- R2 两件齐: `Mzk1ULR2HsQSupportActual.{hsQ_actualSupport,hsQ_actualSupport_split,hsQ_actualSupport_bound}` 16:21:39 + `hlogdK_tower` 16:26:28。
