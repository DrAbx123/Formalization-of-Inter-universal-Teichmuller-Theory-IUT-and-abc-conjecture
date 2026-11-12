# Decomposition pairing candidates (A991, revised A994)

| field | value |
|---|---|
| Status | PARTIAL (未过判定点；候选陈述草案 + 来源/归一化/非负条件已列，无一候选对实际数据成立) |
| 版本钉住 | lana 引用按根 Iut/ 树 + 行号；无手动编译；文件仅为本轮设计文档 |
| 判定点 | 需要证明任一候选的逐位（或分组）不等式，当前全部 OPEN |

## 0. 目标与分解口径

目标 M := V - (sF-1)*A >= 0，其中
- A = |log q| = logQ/(2l)，logQ = sum_w weight_w * ord_w(q_w) * log p_w（lana Iut/Cor312/LeftHandSide.lean:81-88，absLogQ = logQ/(2*l)）；
- V = logVol(hull(vcI))；lana Iut/WallEquiv/VcI.lean:741 logVol_hull_vcI_eq: V = (sum_i sum^fin_{vQ} hullPacket_i vQ) / nC（nC = l* = (l-1)/2，Iut/Wall/Rss.lean:303）；
- variant_of_ss_gap（Iut/WallEquiv/Gap.lean:523）: SSIneq D -> Corollary312Variant；gapHullAt（同文件 :895）: 逐位 gap 项 sum_c w_c * ind2Term；
- 权重归一：weight_w = f_w/[F:Q] 为 normalized degree weight，sum_w weight_w = 1（按 AbsLogQ 定义归一化所用口径）；w_c 为 tuple weights，sum_c w_c = 1（tupleWeight 归一化，lana LocalTheory 的 tuple weight 约定）。该两条归一化在本文档中作为口径记录：它们进入 logQ/H_v 的具体数值，任何候选不等式的常数都依赖此口径。

逐位分解（A911 固有分配）：
M = sum_{v finite} (H_v - T_v) + (H_inf - arch_expected) - torsion_terms，其中
- T_v = (sF-1) * weight_v * ord_v(q_v) * log p_v / (2l)；
- H_v = (1/nC) * sum_i hullPacket_i(v)；
- H_inf = (1/nC) * sum_i hullPacket_i(inf)。

## GAP-A: archimedean equivalence NOT proved

Paper normalization uses arch = log(sqrt 2 * pi)（Mzk1DifferentDictionaryActual.archConstant），但实际对象是 H_inf = (1/nC) * sum_i hullPacket_i(inf)（lana VcI.lean archDefect 项，Gap.lean:700）。恒等式 H_inf = log (sqrt 2 * pi)（或 H_inf = (1/nC) * nC * log(sqrt 2 pi)）NOT proved；是 GAP。C4 及任何使用 arch 的候选依赖此未证识别。

## GAP-B: torsion entry NOT fixed

Paper 字典有 torsion 项 r/n（Mzk1DifferentDictionaryActual.torsionTerm），但其在不变量和中的确切位置（是否从 V 减去、是否在 archimedean 项内、是否与 different 抵消）NOT determined；符号与归一化是 GAP。C1/C2/C4 不得静默假设符号。

## Candidate C1 (per-place; MODEL/PARTIAL)

- 来源：T_v 如上；H_v 的精确有限位公式 hullPacket_finite = sum_c w_c sum_j rho_{cj} log p（lana VcI.lean:806 区域；green 算术副本 Mzk1HullPacketFormulaActual），tame 情形 sum_c w_c sum_j (1 - 1/e_{cj}) log p（VcI.lean:844）。
- 陈述草案：C1Bound v := T_v <= H_v；(forall v, C1Bound v) -> 0 <= M（去掉 arch/torsion 分项后由 Finset.sum_nonneg + linarith）。
- 非负充分条件：H_v >= 0 已在 tame 情形由 green 公式推出；但 ramified 位 H_v 可为负（rho 可负），因此 C1 不能无条件成立；需要逐位估计 H_v 下界。
- 循环性警示：C1 的充分条件不得引用 M >= 0 或 SSIneq 本身；本候选是目标的分项形式。

## Candidate C2 (bad-prime grouping + tame buffer; MODEL/PARTIAL)

- 来源：tame hullPacket_tame（VcI.lean:844）；缓冲项 (1 - 1/e_p) log p 出现在 tame 展开中。
- 陈述草案：C2Bound p := sum_{v|p} T_v <= sum_{v|p} H_v + (1 - 1/e_p) log p；(forall p, C2Bound p) -> 0 <= M（按素数分组求和）。
- 非负充分条件：e_p >= 1（ramification index），且 buffer 未被 H_v 重复计入；若 H_v 已包含 tame 展开的 (1-1/e) 项，buffer 会重复计数，需明确只用于 wild 位或作为亏空弥补——这是 GAP（口径未定）。

## Candidate C3 (capsule/label weighted; IDENTITY-level, green)

- 来源：thetaSumPaper_eq_clana_mul（green，Mzk1PaperNormThetaActual）：sum_i sum_j ((j^2-1)/(2l)) A / nC = c_lana A，c_lana = (sF-1)/(2l)；c_lana 与 ssCoeff 的关系在 Mzk1RDefinitionAuditActual 记录。
- 陈述草案：C3Identity : (1/nC) * sum_i sum_j ((j^2-1)/(2l)) A = c_lana A（green）；但 c_lana A 只是 (sF-1)A 的恒等重写，不提供正性。
- 结论：C3 是恒等层，不能单独推出 M >= 0；须与 C1/C2 的正性配合。

## Candidate C4 (global arch; PARTIAL/GAP)

- 来源：archConstant = log(sqrt 2 * pi)（Mzk1DifferentDictionaryActual）。
- 陈述草案：C4Bound (deficit : R) := deficit <= arch；deficit + arch - torsion >= 0 -> 0 <= M。
- GAP：deficit 未定义（应为 sum_v (T_v - H_v) 的正部）；H_inf = arch 未证（GAP-A）；torsion 符号未定（GAP-B）。数值上 arch 约 1.4913，仅能覆盖 p ∈ {2,3} 量级亏空。

## Candidate C5 (wild e>1 buffer; PARTIAL)

- 来源：different/ramification 的 1/e 项（Mzk1DifferentDictionaryActual.diffPaperPerPlace 中的 -order*logp - r/n + arch；具体 1/e 出现在 logMuPaper 系数）。
- 陈述草案：C5Bound p e := T_p <= H_p + (1/e) log p。
- 非负条件：需 H_p 包含至少 (1/e) log p 的额外正贡献；对 Q_p(zeta_p) 的 tame 展开是 (1 - 1/(p-1)) log p（与 1/e = 1/(p-1) 同阶），方向上可行但未证明。

## Candidate C6 (G-constrained grouping; MODEL-level green)

- 来源：链二模型 Mzk1Chain2CoreActual（g1_union_eq_single, g3_width_bound, survival_iff）。
- 陈述草案：C6Bound S := sum_{v in S} T_v <= sum_{v in S} H_v + arch - torsion；C6Bound univ -> 0 <= M；G1 型把 S 塌缩为单点，G3 型给宽度预算。
- 非负条件：模型级条件已 green；真实数据需 SourcePilotRegionLGeneric 实例（A966）与真实 H_v，当前 GAP。

## 逐项非负清单与循环性说明

| 项 | 非负所需 | 状态 |
|---|---|---|
| H_v tame 位 | green 公式（sum rho log p） | tame: 非负；ramified: 可负 |
| buffer (1-1/e)log p | e >= 1 | green（需 e 定义口径） |
| arch | log(sqrt 2 * pi) >= 0 | paper级；Mathlib 界未证 |
| torsion | r/n >= 0, r <= n | green 算术（torsionTerm_nonneg/le_one）但符号位置 GAP-B |
| deficit | 定义 + H_inf = arch | GAP-A |

循环性：以上任何候选的充分条件都不得包含 M >= 0、SSIneq、或 H_inf = arch 的结论作为假设；C4 若把 H_inf = arch 当假设即循环，故标 GAP-A。

## 结论

全部候选为 PARTIAL：形式化陈述与来源/归一化口径已写清；arch 等价（GAP-A）、torsion 位置（GAP-B）、ramified H_v 下界、deficit 定义均未闭合。C3 为恒等层。无候选对实际数据成立，不得作为 M >= 0 的证据。
