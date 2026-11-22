# C2 / Q-M 口径审计（david, 2026-11-17）

## 1. 事实（Lean 定义/定理，行号）

- actualQPilotMagnitudeClassical (PaperLevelXiFTargetActual:57) = Σ_b nativeBadLocalWeight_b · qVFamNormalizedCoefficient_b · log(qVFamTensorP_b); weight = nativeBadLocalWeight = localNormalizedWeight(K_w) = 1/[K_w:Q_p] (VbadPlaceIndexingActual:89-98). 该量无显式 1/(2l) 因子（Q-尺度）。
- actualRootCoeff (PaperLevelXiFTargetActual:67) = c_norm/(2l)。
- actualRootThetaRegion/Hull (82-96) 用 c_norm/(2l) 作区域系数 ⇒ hull log volume 是 M-尺度（q^{1/(2l)} 方向）。
- actualThetaHullLogRoot (116) = Σ_b nativeBadLocalWeight_b · actualLocalHullLog_b。
- p6SandwichChain_neg_M_le_HTheta (Mzk1P6HCor312SandwichChain:26): -actualQPilotMagnitudeClassical ≤ actualThetaHullLogRoot; 定理名写 -M，但语句左端是 Q-尺度 actualQPilotMagnitudeClassical。

## 2. 直接结论（疑似命名/尺度不一致）

- θ 的 hull 体积按 c_norm/(2l) 建 ⇒ θ 是 M-尺度。
- P5 下界语句 -Q_actual ≤ θ_M（Q 对 M 不等）；若证明真按 M 尺度算，则 actualQPilotMagnitudeClassical 必须已含 1/(2l)（c_norm 实为 ord/(2l) 或 weight 含 1/(2l)）——需用 qVFamTensorCoefficient/qVFamNormalizedCoefficient 的 exact 定义核对（本轮 grep：c_norm=qVFamTensorCoefficient=order，不含 1/(2l)）。
- 因此 legacy 下界不能自动当 -M ≤ θ；C2 q 下界要么 (a) 证 actualQ = M_paper_v2（很可能不成立，见 §3/§4），要么 (b) 走 route J1 局部 Kummer 质量恒等式 (1/2l)log|q| = log|r| + 区域包含，直接造 -M≤θ，要么 (c) 改 θ 系数归一使成 Q-尺度（则 θ≠paper Θ）。

## 3. v2 的 Fmod-层化简（fiber_sum_ef + 赋值塔）

对 q ∈ Fmod base change 到 F:
- ord_P(q) = e_{P|b}·ord_b(q)（P|b）；
- Σ_{P|b} e_P f_P = [F:Fmod]（Mathlib Ideal.sum_ramification_inertia，已落 Mzk1ULFiberSumActual.fiber_sum_ef）。
则 qPilotMagnitudePaper_v2 = (1/[F:Q])Σ_b Σ_{P|b} f_P ord_P(q) log p_b = (1/[F:Q])Σ_b (Σ e_P f_P) ord_b log p_b = (1/[F:Q])[F:Fmod]Σ_b ord_b log p_b = (1/[Fmod:Q])Σ_b ord_b(q) log p_b。
⇒ M_paper_v2 = (1/(2l))·(1/[Fmod:Q])Σ_b ord_b(q) log p_b（Lead 的 Fmod 加权和，无需 per-fibre choice）。

## 4. actualQ 与 v2 的权重差

actualQ = Σ_b (1/[K_w:Q_p]) c_norm_b log p_b，c_norm = ord_w(q)。局部度塔: [K_w:Q_p] = e_{w|P} f_{w|P} · e_{P|b} f_{P|b} · e_b f_b；ord_w(q) = e_{w|P} e_{P|b} ord_b(q)；⇒ 系数 = ord_b(q) / (f_{w|P} f_{P|b} e_b f_b)，而 v2 系数 = ord_b(q)/[Fmod:Q]（每 b 一次）。差一个 f_{w|P} f_{P|b} e_b f_b / [Fmod:Q] 因子——F/Fmod 非无分歧时 ≠1。
⇒ actualQ ≠ M_paper_v2 一般；v2 只作审计表达（docstring 标）。

## 5. 判决建议

1. C2 q 下界 -M ≤ θ：用 J1 局部 Kummer 质量路线（(1/2l)log|q|=log|r| + 区域包含），以 M_paper_v2 = Fmod 加权和为目标；legacy -actualQ ≤ θ 不能直接给出。
2. C3-upper（θ ≤ H_pkt paper 上界）是真正剩余；H_pkt 权重须与 θ 同尺度/同域（已核 λ/d_mod 权）。
3. actualQPilotMagnitudeClassical 与 Fmod 加权和的关系：需再证 c_norm=ord_w(q) 的 exact 展开 + 局部度塔恒等式；若保留 legacy，须在 docstring 标 LEGACY 并说明与 paper Q 的差异因子。
4. 动作：kurt J1 桥为 C2 下界正解；david 给 fiber_sum_ef（已落）+ ord_P(q)=e_P ord_b(q)（下一批）；sophie/Lead 定 C3-upper 权接口。

## 6. 参考

- route §5.3 L395-406 (C2); §5.4 L459-472 (Q/M/S_ar)。
- IUT IV L1303-1353 (q^ADiv/fFADiv), L1214-1235 (Def1.9), L1705-1743/L1860-1878 (Step v/viii weights)。
- Lean: PaperLevelXiFTargetActual:57/67/82/116; Mzk1P6HCor312SandwichChain:26; VbadPlaceIndexingActual:89; Mzk1ULQPilotMagnitudeV2Actual:36-122; Mzk1ULFiberSumActual。
## 7. 与 kurt 的配合（本轮判决后的接口）

### 7a. ord 塔与 Σef（已落/下一批）
- 已落: `Mzk1ULFiberSumActual.fiber_sum_ef`（Mathlib `Ideal.sum_ramification_inertia` 的 primesOverFinset 实例化，R=𝓞Fmod, S=𝓞F）: Σ_{P|b} e_P f_P = [F:Fmod]。
- 下一批 `Mzk1ULOrdFiberTowerActual`: ord_P(q)=e_{P|b}·ord_b(q)（q∈Fmod）。Lean 依赖: `Ideal.ramificationIdx'_algebra_tower`（Ramification.lean:394，P.under 的 e 塔乘性）+ 局部赋值/`localNormalizedWeight` 展开；再由 Σef 得 `M_paper_v2=(1/(2l))(1/[Fmod:Q])Σ_b ord_b logp`。

### 7b. 2l-root hull scaling（若走 M-尺度 θ 路线）
- 现成 donor: `Mzk1C3BlockThetaExpActual.c3PacketNormalizedLogVolume_pow_prime_smul`（:77）与 `_pow_sq`（:90）:
  `c3PacketNormalizedLogVolume C3 μ (p^m • S) = -(m log p) + c3PacketNormalizedLogVolume C3 μ S`（hpos/hfin）。
- 这是整数 p-power 缩放; 2l-root 需要 **分数指数 q^{c/(2l)}**（c=c_norm）的 log-shell 缩放，即缺失的 **2l-root hull equality datum**:
  `hull(q^{c/(2l)}·S) 的 normalized log volume = -(c/(2l))·log q + hull(S)`（Kummer 根扩张/对数壳）。
- 结论: legacy P5 下界的 -Q≤θ 不能升级为 -M≤θ，除非该 datum 成立; 若成立则 θ 可由 M-尺度 region 直接读。

### 7c. URC2 q_P5 切口径
- `Mzk1URC2AssemblyActual.qP5 := -M_paper_v2`（已定义）; 其下界 `qP5 ≤ ksThetaHullLogRoot_lam` 需 **M-尺度 θ**（7b datum）或 J1 局部 Kummer 质量路线（route J1: (1/2l)log|q|=log|r| + 区域包含），不能用 legacy -actualQ≤θ。
- 若走 J1: 目标 `-M_paper_v2 ≤ θ_Lam` 的右端仍是 θ（Q-尺度）⇒ 需先用 7b 把 θ 换成 M-尺度; 否则 J1 输出应为 M-尺度的质量下界对象。
- 动作: kurt 决定 J1 输出对象尺度; david 提供 7a 与 7b 的 Lean 接口; Lead 裁 C3-upper 权域（λ/d_mod）。

## §8 kurt: scale chain verdict (2026-11-17 01:05Z)

Definitions read in this round (K-side):
- ksThetaCoeff (Mzk1URThetaKSideActual:76) = (gaussExponent j).toNat * actualRootCoeff, and
  actualRootCoeff = c_norm/(2l)  => ksThetaRegion/Hull are M-scale (root coefficient).
- ksGaussK/ksCeilC (:96,:102) = ceil(actualRootCoeff * e) / e  => urCeilC is the M-scale ceiling.
- urPacketV_K (:130) = (-ksCeilC + ksDifferentOrder + 1) * ksLogP + ksExceptionalSum  => the packet
  value V is M-scale.
- ksThetaHullLog (:135) = normalized log volume of the M-scale theta hull; ksThetaHullLogRoot_lam =
  sum_b thetaLamWeight_b * ksThetaHullLog_b (rfl, see Mzk1URThetaKScaleActual).

### Answers to (a)-(c)

(a) Q scale does NOT appear in the K-side lambda chain. H_pkt := ucWeightedHpkt (thetaLamWeight T) V
    with V = urPacketV_K (M-scale). Hence no HpktM := H_pkt/(2l) is needed; the M-scale H_pkt is the
    right C4 object.
(b) htheta: ksThetaHullLogRoot_lam_le_ucWeightedHpkt_lam is M-scale on both sides (theta_M <= H_pkt).
(c) C3 upper RHS kappa*(A - c_l*Q) - M: Q and M are q-scale (Q = v2, M = Q/(2l)); A must be taken
    at the same q-scale (A/M = A/(2l) if A is the q-scale target; A_M must be provided by the C3
    files). The theta object is M-scale, so the C3 inequality to prove is at M scale:
    H_pkt(M) <= kappa*(A_M - c_l*Q_M) - M, with Q_M := Q/(2l) = M_paper_v2.

### End-to-end chain (with scales)

Step 1 (M-scale C2 lower). We have UNCONDITIONALLY
  -(sum_b thetaLamWeight_b * urCeilC_b * log p_b) <= theta_M   (Mzk1URThetaKHP5LamActual).
  To obtain the route C2 lower -M_paper_v2 <= theta_M we still need
  (J1-M)  M_paper_v2 <= sum_b thetaLamWeight_b * urCeilC_b * log p_b.
  (J1-M) is exactly the weighted Kummer/telescoping inequality: per-b local Kummer mass
  (1/[L:Q_p]) log(mu(rO_L)/mu(O_L)) = (1/(2l)) log|q|_p, region containment rO_L subset theta hull,
  and the Fmod degree telescope from david's fiber_sum_ef.
Step 2 (C2 upper, M-scale). theta_M <= H_pkt: accepted (ksThetaHullLogRoot_lam_le_ucWeightedHpkt_lam
  with hperB; the actual per-b V is urPacketV_K once kurt's actual packet instantiation compiles).
Step 3 (C3 upper, M-scale). H_pkt <= kappa*(A_M - c_l*Q_M) - M (real C3 gap; waits for hlogK/hsQ
  letters and the A_M scale choice).
Conclusion: -M <= theta_M <= H_pkt <= kappa*(A_M - c_l Q_M) - M  =>  c_l Q_M <= A_M.

### Ruling

- The scale chain is consistent once (J1-M) is proved: the theta side and H_pkt are both M-scale,
  and no 2l-root hull scaling datum is needed for this formulation.
- The legacy calibration file Mzk1URThetaKMScaledActual (neg_actualQM_le_thetaM) uses
  actualThetaHullLogRoot, i.e. the GAMMA-weighted P6/PaperLevel object, NOT the C4 lambda object
  ksThetaHullLogRoot_lam. It is a valid M-scale lower bound for that object, but it does not by
  itself provide C4's htheta input. Linking actualThetaHullLogRoot to ksThetaHullLogRoot_lam is a
  separate weighted comparison (gamma vs lambda family) and is NOT proved.
- Therefore J1-M-scale (J1-M above) remains NECESSARY for the route C2 lower unless one proves the
  gamma/lambda weighted comparison; it is not eliminated by the legacy calibration.
- J1 per-fibre (v2 fibre-order crosswalk) remains audit/alternative only (base-change tower route).

## §9 A_M caliber for C3 upper (kurt, draft for david/andrew confirmation)

C3 upper target in M scale: H_pkt(M) <= kappa*(A_M - c_l*Q_M) - M, with Q_M := M_paper_v2 = Q/(2l).
- H_pkt := ucWeightedHpkt (thetaLamWeight T) V, V = urPacketV_K, already M scale (see §8).
- Q_M = M_paper_v2: q-scale divided by 2l (david's Q = qPilotMagnitudePaper_v2, M = Q/(2l)).
- A: if paperA is defined at q scale (same family as Q), then A_M := A/(2l); if A is already at the
  theta/target scale (i.e. built from root coefficients), A_M := A. This must be fixed by reading
  the actual definition used in C3 (Mzk1P6HThetaUpperSandwichActual / KappaLemmaActual) - david/
  andrew to confirm. No guess is used in code until confirmed.
- kappa and c_l: dimensionless / scale-free constants (from KappaLemmaActual), unchanged by the
  M-scaling as long as both sides are consistently divided by 2l.
Pending: exact A declaration, then a one-line lemma A_M = A/(2l) (or A_M = A).

### §9 final (Lead ruling 2026-11-17 01:35Z): no A_M rescaling

C3 upper is the route's single real inequality (route L485-487):
  H_pkt <= kappa*( (1 + 12*d_mod/l)*S_ar + 2 log l + 56 - c_l*Q + (20/3)*l*_mod log(s<=) ) - M.
A := (1 + 12*d_mod/l)*S_ar + 10*E_ar, c_l = 1/6 - 12/l^2, Q = route Q (= v2, q scale),
M = Q/(2l). A and c_l*Q are in the same height family (Q scale); there is NO A_M = A/(2l).

Exact declarations (verified):
- paperA : Mzk1ULHpktActual.paperA (d_mod l S_ar E_ar : Real) -> Real (:31)
- kappa/cL/paperEar/Ear: same file
- Hpkt_le_weighted_bound : Hpkt w V <= Sum w*B from V <= B pointwise
- ul_hpaper_of_stepVIII (hl, hE, hprime: lstar_logs <= (4/3)E_ar, hconst: 2 log l + 56 <= (4/9)E_ar,
  hstepVIII) : H <= kappa*(paperA - cL Q) - M
- ul_hpaper_assembled : (Sum w*B <= kappa*(... ) - M) => Hpkt <= kappa*(paperA - cL Q) - M
- ul_hpaper_assembled_paperConstants : paper constants version (uses ul_hconst_of_paperConstants)

Target C3_upper_route (same RHS as UCC4 hstepVIII up to the paperLstarLogs (4/3)E_ar absorption):
  ucWeightedHpkt (thetaLamWeight T) V <= kappa l * (paperA d_mod l S_ar E_ar - cL l * Q) - M
with Q := qPilotMagnitudePaper_v2 (or actualQPilotMagnitudeClassical at q scale; david to fix the
exact Q declaration), M := M_paper_v2, V := urPacketV_K (M-scale packet values).

Letters still needed for C3 upper: hlogK/hsQ (david) to supply hstepVIII, plus
lstar_logs <= (4/3)*E_ar (hprime); the 2log l + 56 <= (4/9)E_ar part is already
ul_hconst_of_paperConstants. C4 conclusion unchanged: c_l*Q <= A.

### §9b (2026-11-17 02:05Z) cross-ref: david Q-NORMALIZATION-AUDIT verdict

david's coord/Q-NORMALIZATION-AUDIT.md (paper line refs) rules:
- paper Q normalization is 1/[F:Q] (Def1.9 L1214-1235, weight f_P/[F:Q]) => v2 IS paper Q_all.
- StepV collectionBound's per-b Q is the LOCAL q quantity (c_norm*log p, IV L1705-1743);
  hstepVIII's hM uses nativeBadLocalWeight (1/[K_w:Q_p]) => with Q_i = c_norm log p it yields
  legacy actualQ/(2l), NOT M_paper_v2.
- C2 and C3 must share the same M (p6_sandwich_cancel); legacy -actualQ <= theta does not give
  -actualQ/(2l) <= theta. So C2's M-scale lower bound still needs J1-M (or the 2l-root hull equality).
Recommendation (david, consistent with kurt audit sections 2/4/7):
- C3-upper: close with legacy StepV-Q + actualQ/(2l) now, docstring marked LEGACY.
- C2: J1-M route with M := M_paper_v2.
- v2 stays the paper Q_all audit expression; the C2 (Q_all) vs C3 (StepV-Q) slot difference is a
  route-level interface: their connection (lambda/d_mod weighted average + Sum ef) is UNPROVEN and
  must be listed as such, not silently assumed equal.
C3_QM_alignment remains on hold; when closed under the legacy caliber its hQ instantiates with
Q_b = c_norm_b*log p_b (rfl-level from actualQPilotMagnitudeClassical's definition); under the
v2 caliber the outer weight must be rebuilt (1-2 batches).

### §9c (2026-11-17 02:25Z) plan (B): unify on v2 / M_paper_v2 (main line per david §5)

david's Q-NORMALIZATION-AUDIT section 5 (paper line refs) rules:
- paper Q normalization = 1/[F:Q] with f_P weights (Def1.9 L1214-1235) => v2 is paper Q;
  1/[K_w:Q_p]/actualQ are StepV-local/legacy.
- StepV collectionBound's per-b Q = local q-pilot quantity c_norm*log p (IV L1710-1740; route
  L376-383); the global quantity is assembled by lambda/d_mod (L1705-1743) or Step viii
  (L1860-1878).
- Step 5.4 C3's Q = global q-divisor degree = step 6.2 h = Q_all = v2 (1/[F:Q]); the step 6.2
  selected-Q is a different quantity (Q_selected). C2 and C3 must share the same Q object.
- J1-M target: -M_paper_v2 <= theta_lambda (M_paper_v2 = v2/(2l); the Kummer weight uses
  1/[F:Q]*f_P fibre weights, expanded to the Fmod level via Sum ef).
- Legacy StepV-Q + actualQ/(2l) does NOT match D4's Q = h; recommendation: main line (B).

(B) implementation plan (1-2 batches):
1. Rebuild the StepVIII outer weights at lambda/d_mod: define the weighted intermediate
   HstepVIII_lambda := Sum_b thetaLamWeight_b * B_b with B_b the per-b paper StepV bound
   (urPacketV_K), and re-derive the accompanying hVh / collectionBound instantiation with the
   v2 per-b Q_i := (1/[F:Q]) * Sum_{P|b} f_P c_P log p_P (NOT nativeBadLocalWeight * c_norm log p).
2. Prove hM_lambda : M_paper_v2 = Sum_b thetaLamWeight_b * Q_i_b / (2l) using david's
   MpaperB decomposition and fiber_sum_ef / Sum ef (need the per-b v2 term identity).
3. Then C3_upper_route_legacy stays as INTERIM only; the terminal C3 uses the lambda-weighted
   hstepVIII and M_paper_v2 (same M as C2's J1-M output).
Open interfaces to be proven (not assumed): Q_i per-b definition match, lambda-weight vs
f_P/[F:Q] normalization bridge, Sum ef telescope.

## ADDENDUM 2026-11-18: R0.1 route-aligned c_P ruling (SUPERSEDES the order-caliber note)

Route `coord/P7-G1-P6-P8-CLOSURE-ROUTE-20261116.md` §2.1 and §10 (item 1) fix the paper
dictionary.  The earlier ruling "c_P = order, no /e" is **SUPERSEDED**:

- route §2.1: `v_P(π_P)=1`, `e_P^abs = v_P(p)`, `|x|_P = p^{−v_P(x)/e_P^abs}`, and
  **`c_P = v_P(q_P)/e_P^abs` (R0.1)**;
- `QVFamNormalizedCoefficient`'s actual definition is `−log_p‖q‖`, NOT the integer order
  by name; `QVFamTensorCoefficient`/`qVFamNormalizedCoefficient` carry the raw `v_P` and the
  name is misleading;
- spectral: `spectral = c_P − log(qVFamNormRatio)/log p_b` (S121 form); when
  `qVFamNormRatio = 1` **spectral = c_P (per b)** — NOT spectral = raw order;
- do NOT divide again by e(P/b): e_abs is already inside c_P (route §2.1 explicit warning);
- R0.2 full-fiber uses raw v_P: `(1/[F:Q])Σ_{P|b} f_P v_P(q_P) = f_b v_b/[Fmod:Q]
  = ([Fmod_b:Q_p]/[Fmod:Q])·c_P`; `orderAtFPlace` (=v_P) and `M_paper_v2` are unchanged;
- legacy `actualQPilotMagnitudeClassical` uses spectral:
  `actualQTermSpectral = actualQTermPaper − γ_b·(logratio/log p_b)·log p_b`
  (david's `Mzk1ULR0ActualQCorrectionActual` stays).

Paper anchors: IV L1261-1273 (d_mod=[Fmod:Q], e_mod max ramification, d*_mod=2^12·3^3·5·d_mod,
e*_mod=2^12·3^3·5·e_mod), IV L1275-1294 (Fmod ⊆ Ftpd=Fmod(E[2]) ⊆ F).

### 裁定 2026-11-18 19:26: R0 c_old=e*f*c_P; hprime 只承担 log p 值。R1/R2 同一 Θ: -M <= nu(Theta_paper) <= H_procession; q 格 J_b 只是 Θ 的像。

## VERDICT 2026-11-18 20:03: R0 c_old DONE (exact)

- `Mzk1ULR0COldActual` **DONE 20:03:02**; no sorry; three theorems, all print
  `[propext, Classical.choice, Quot.sound]`:
  - `neg_log_norm_eq_order_div_e` (from the S829 formula with N=p^f, d=e f:
    `-log_p||q|| = v/e`);
  - **`cOld_eq_ef_mul_cP : c_old = e*f*c_P`**;
  - **`cOld_eq_cP_iff_ef_one`** (equality only when `e*f = 1`; no general equality assumed).
- Log also contains one stale infra line (`Mathlib/Order/Directed.olean` read failure) from an
  earlier attempt; the DONE verdict is current.


## VERDICTS 2026-11-18 20:03 (exact, re-confirmed)

- `Mzk1ULR0COldActual` **DONE 20:03:02**:
  `neg_log_norm_eq_order_div_e` → `[propext, Classical.choice, Quot.sound]`;
  `cOld_eq_ef_mul_cP` → `[propext, Classical.choice, Quot.sound]`;
  `cOld_eq_cP_iff_ef_one` → `[propext, Classical.choice, Quot.sound]`;
  source: no sorry.  (Stale infra line `Mathlib/Order/Directed.olean` in log is from an
  earlier attempt.)
- `Mzk1ULR0D1WiringActual` **FAIL 20:03:27 = INFRA**: log size 171 bytes, single line
  `Mzk1ULR0D1WiringActual.lean:5:0: error: failed to read file
  '...\LeanFormal\IUT\Foundations\NumberField\Places.olean'` (empty-of-code-content log,
  dependency olean read failure; not a code verdict).

### 2026-11-18 21:1x route reading: paper coefficient = c_P/(2l), c_P=v/e_abs (spectral)=cNorm; route paper Theta = rootNormHull (rootHalfCoefficient). Raw-order qVFamPaperRootCoefficient=order/(2l)=e*c_P/(2l) is an e-scaled different object. No normRatio=1 needed for route R1; previous unconfirmed claim retracted.
