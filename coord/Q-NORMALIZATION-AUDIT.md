# Q 归一化对账（david, 2026-11-17）—— paper 行号 + 判决

## 1. paper 的 q-pilot/Q 归一化

- **Def 1.9（IV L1214-1235）**：`deg(a) = (1/[F:Q]) Σ_v c_v log q_v`（normalized degree，分母 **[F:Q]**）；`|log q| := (1/2l) log q`（L1359-1364）；`log(q) := deg(q^ADiv)`（L1324-1333）。
- **q^ADiv / fF^ADiv（IV L1303-1313, L1340-1353）**：q^ADiv 由 q-参数（Tate 参数 q_v）构成；fF^ADiv support=Supp(q^ADiv)，系数全 1（conductor）；log fF = deg(fF^ADiv)（同样 **[F:Q]** 归一）。
- **Step(v) 的 λ-平均（IV L1705-1743）**：λ_e := [(F_mod)_v : Q_{vQ}]（L1717-18）；Prop 1.7 分母=纤维总度；全局 Σ_{v|vQ} λ_v = [F_mod:Q]（L1736-41）；Step(viii) 外层 sum over vQ 无额外权（L1860-1878）。
- **c_norm 的 spectral/order 归一**：paper 的 q-参数系数取 `ord_p(ϖ)=j²/(2l)·ord_p(q_v)`（Step(v) local bound, route L376-383/IV L1710-1740），即 **norm 系数 c_norm = ord/e 的归一（spectral 1/(2l)）**；paper 没有在 Q 上再乘 1/[K_w:Q_p]。

## 2. 判决

1. **paper 的全局 Q（h=Q_all）归一 = 1/[F:Q]，权 f_P/[F:Q]（Def1.9）⇒ v2 是 paper Q**。
2. `nativeBadLocalWeight = 1/[K_w:Q_p]`（VbadPlaceIndexingActual:89-98）与 `actualQPilotMagnitudeClassical = Σ weight·c_norm·log p` 是 **legacy/StepV-式局部归一**，与 paper Q 差 f/e 因子（审计 §4：系数差 f_{w|P}f_{P|b}e_b f_b/[Fmod:Q]）。
3. StepV `collectionBound` 的 per-b `Q` 在 paper 中 = **该 b 的局部 q 量（c_norm·log p，c_norm=order/ spectral 归一）**，不是全局归一 Q_all；它在 Step(viii) 外围再由 λ/d_mod 权平均成全局量。
4. `hstepVIII_of_paperLetters` 的 `hM : M=Σ nativeBadLocalWeight·Q/(2l)` 用的是 **1/[K_w:Q_p] 权** ⇒ 若 `Q_i=c_norm logp`，得到 **M=actualQ/(2l)**（legacy），**不是 M_paper_v2**。

## 3. C2/C3 槽的判定

- **C2 与 C3 必须用同一个 M**（p6_sandwich_cancel 需要同 M 相消；route L397-404 的 C2 是 q_P5=-M 与 θ≤H_pkt，M 与 C3 的 M 是同一符号）。
- **C3-upper 的 Q/M 槽**：若保持 hstepVIII 现状（nativeBadLocalWeight 权），只能得 legacy `Q=actualQ`、`M=actualQ/(2l)`；若要用 v2/M_paper_v2，必须把 hstepVIII 的外层权换成 λ/d_mod 并重证 per-b q 量/Σef 对账（1–2 批）。
- **C2 q 下界**：即使同意 Q=actualQ，legacy `-actualQ ≤ θ` **推不出** `-actualQ/(2l) ≤ θ`（−actualQ/(2l) > −actualQ），故 C2 的 M-尺度下界仍需 J1-M 质量路线或 2l-root hull equality。这与审计 §2/§7 一致。
- 结论：**C3-upper 用 legacy StepV-Q+actualQ/(2l) 可立即闭合其 Q/M 槽（标 LEGACY）；C2 的 -M≤θ 必须走 J1-M（M=M_paper_v2 或 actualQ/(2l) 由 J1 输出决定），不能由 legacy 下界升级**。v2 保留为 paper Q_all 的审计表达（C2 的 Q 定义与 C3 的 Q 槽若不同须在 route 层说明：C2 用 Q_all，C3 用 StepV-Q，二者由 Σef/λ 平均连接，连接等式是未证接口）。

## 4. 参考

- IV L1214-1235 (Def1.9), L1303-1353 (q^ADiv/fF^ADiv), L1705-1743 (Step v λ), L1860-1878 (Step viii), route L397-404 (C2), L459-472 (Q/M).
- Lean: PaperLevelXiFTargetActual:57/67/116; VbadPlaceIndexingActual:89; StepVProcessionAverage:35; Mzk1ULHpktActual:91/191; Mzk1ULStepVIIIActual:576; Mzk1ULQPilotMagnitudeV2Actual:36-122; coord/C2-CALIBER-AUDIT.md.
## 5. 对 Lead 四问的判决（1 批，paper 行号）

**① Q 的归一化是哪一种？** paper 的全局 Q（h=Q_all、C3 的 Q、C4 的 Q）用 **1/[F:Q] + degree 权 f_P（Def1.9, IV L1214-1235）** ⇒ **v2 是 paper Q 的正确归一**。`nativeBadLocalWeight=1/[K_w:Q_p]` / `actualQPilotMagnitudeClassical` 是 **StepV 局部/legacy 归一**（VbadPlaceIndexingActual:89-98），不是 paper 全局 Q（差 f/e 因子，见 §4/§C2 审计）。

**② StepV collectionBound 的 per-b Q 对应 paper 什么量？** 它是 **该 b 的局部 q-pilot 量**：c_norm·log p_b，其中 c_norm 是 q-参数的 **spectral/order 归一**（paper Step(v) 的 `ord_p(ϖ)=j²/(2l)·ord_p(q_v)`，IV L1710-1740；route L376-383；c_norm=order/e 的 e 归一来自局部 ramification 归一，L1717-1718 λ_e 与 Prop1.7 分母）。它不是全局 Q_all；全局量由外层 λ/d_mod 权（L1705-1743）或 Step(viii)（L1860-1878）组装。

**③ 三个 Q 是否同一对象？**
- route §5.4 C3 的 Q（L462）= **全局 normalized q-divisor degree** = §6.2 的 h = Q_all（L577-579 的 h 定义），与 Def1.9 同归一（1/[F:Q]）⇒ **= v2**。
- §6.2 的 **selected Q**（L579: 进入当前 initial Θ-data 的选定位之和）= 选定 lift 之和（D2 的 Q_selected，我的 `Mzk1ULSelected` 计划）；它是一个 **不同的量**（h−Q 是遗漏位）。
- C2 的 **M=Q/(2l)**（L397-404/L462-463）中的 Q 若指 h=Q_all，则 M=M_paper_v2；若 C3 的 Q 槽用 StepV 局部/legacy 量，则其 M 不同 ⇒ **C2 与 C3 必须用同一个 Q 对象**，否则 sandwich 不能相消。

**④ J1-M 的目标**：应为 **`-M_paper_v2 ≤ θ_λ`**（M_paper_v2 = qPilotMagnitudePaper_v2/(2l)，paper Q_all 口径；J1-M 的 Kummer 质量权应取 **1/[F:Q]·f_P** 的 fiber 权，经 `Σef`/λ-平均展开为 Fmod-层 `(1/(2l))·(1/[Fmod:Q])Σ_b ord_b logp`）；**不是** `-actualQ/(2l)`（actualQ 是 legacy 1/[K_w:Q_p] 归一，J1 的局部质量公式 `(1/2l)log|q|=log|r|` 与 paper Q 的 degree 权一致，不与 legacy 权混）。若主线 C3 暂用 legacy StepV-Q+actualQ/(2l)（方案 A），则 C2 也须用同一 legacy M——但那样 C2 与 D4 的 Q=h=jHeight 不匹配（andrew 已报），故 **主线应选 (B)：统一 v2/M_paper_v2，C3-upper 外层权改 λ/d_mod**；方案 A 仅作临时绿。
## ADDENDUM 2026-11-18: c_P caliber per route §2.1 (supersedes order-caliber section)

- paper/route c_P is `v_P(q_P)/e_P^abs` (route §2.1 R0.1), with `e_P^abs = v_P(p)`, 
  `|x|_P = p^{−v_P(x)/e_P^abs}`;
- the raw integer order (`qVFamily).order` = v_P(q_P)) is NOT the paper c_P;
- `QVFamNormalizedCoefficient` is `−log_p‖q‖`; spectral value equals c_P iff 
  `qVFamNormRatio = 1` (S121);
- IV L1261-1273: d_mod=[Fmod:Q], e_mod = maximal ramification index of Fmod over Q,
  d*_mod=2^12·3^3·5·d_mod, e*_mod=2^12·3^3·5·e_mod (so e_mod ≤ d_mod);
- R0.2 full-fiber keeps raw v_P (orderAtFPlace) — unchanged; M_paper_v2 = (1/2l)ΣQb unchanged;
- no double division by e(P/b).

### 2026-11-18 20:03 Mzk1ULR0COldActual DONE 20:03:02: neg_log_norm_eq_order_div_e / cOld_eq_ef_mul_cP / cOld_eq_cP_iff_ef_one all clean trio; c_old=e*f*c_P, equality iff e*f=1 (no general equality assumed).
