# NEXT-WAVE-R29 — 严格按交接稿 P0–P7 的下一步（teammate 自主认领）

唯一路线图：D:/iut-audit-20261113/COR312-THREE-ROUTES-HANDOFF-20261113.md（§1–§12，1854 行）。
本文件不是新路线，只是把 §8.2 的 P0–P7 与 §4–§6 三条路线映射到当前仓库状态，供 teammate 认领下一步。任何新任务必须标注它属于哪个 P 步/哪条路线，否则不做。

## P0 — 固定目标与归一化（§8.2 第一步）

状态：对象表完成（coord/HANDOFF-OBJECT-TABLE.md）；paper 系数 c_root=m/(2l) 判定完成（coord/P0-NORMALIZATION-FIX.md）；paper-faithful hull 定义+非零像等式 green。
剩余：
- P0-A：把 paper-faithful 目标陈述在 q 侧也写成 c_root 版（qPilotPaperRegion 的读数链，S800 已有；检查是否还有 c_norm 混入的消费者）。
- P0-B：确认 §2.1 的 (T) 等式 M=A−R=V+gap−(sF−1)A 在仓库实际定义下的 definitional/定理级对应（Mzk1StepVReductionActual 只到纯代数层）。
停止条件：目标是另一 variant 或参照无来源 → 先修接口（§8.2 P0）。

## P1 — 真实张量块与作用矩阵（§8.2 第二步）

状态：多因子块 P1 green + **P2 列张成/行满秩向量形式 green**（integerBasis/generatorColumn/generatorColumn_span_top/fullGeneratorMatrix；DONE 21:22:36Z）。
剩余：
- P1-A：G 矩阵行满秩（列索引改 Option G × L0BasisIndex 后证列张成；SNF 用于指数/体积）。
- P1-B：factorPermutationBlockEquiv 的整数格保持性 + 与来源 Ind1 的等价（当前仅块级 reindex）。

## P2 — 同一 G 的路线一/二联合诊断（§8.2 第三步）

状态：路线一判别完成（公共标量停止条件成立）；路线二工具 green/条件 green；P2 列张成 green；GL_d(Z_p) 保格等号 green（Mzk1MatrixHaarBaseActual）；GAP-DUAL-TRANSPOSE 起点文件已写（Mzk1DualTransposeActual）。
剩余：
- P2-A：G^T S 交格 X_G 的体积公式（接 Mzk1DualIntersectionActual 的 XG）。
- P2-B：交叉核对：路线一有限商指数与路线二对偶交格相对体积给同一数值（不能各造一份增益）。
- P2-C：因子置换/不同 valuation 是否打破公共标量（UNKNOWN；若符合 (A8) 则按 §8.2 P2 停止条件记录，转向来源/全局）。
停止条件：符合 (A8) 且新增估计只依赖 q 无关常数 → 记“该局部生成机制不足”，不再加 orbit 包装。

## P3 — 选定一个真正的新定量引理（§8.2 第四步）

状态：StepV 链、局部 2l 换算、S3014ProcessionData（**StepVExtraNonneg 已闭合**）、S3029AlignmentData、D_exact 条件 L7⇒L6、M≥0⟺L6 条件归约、**DICT-A（Mzk1P3DictionaryActual）** 均 green/条件；素导子类 hD 文件已写（Mzk1PrimeConductorUnconditionalActual，编译迭代）。
剩余：
- P3-A：GAP-P3-DICT —— 实际对象上 M = c·(T(l)·D − e·log p) 的字典（§8.2 P3 的核心）。
- P3-B：StepVExtraNonneg 实际来源（qpilot 新文件 Mzk1StepVExtraNonnegActual 待编译；different/exceptional 非负）。
- P3-C：D_exact 的 arch 项与 L7 下界（与 VbadPlaceIndexing/ArithmeticQPilotLogVolume 对齐；注意 hw 1<=w 与 1/[K:F] 的不相容）。
- P3-D：S3019 的 qPilotIdeal↔bad places 来源识别（按 P3-S3019-BRIDGE.md 的判定：当前不可证，需新对象）。
最小交付：一个具有原文量词的输入类上的明确、可代入界；不合格交付=把比较塞进 structure 字段再投影。

## P4 — 全部允许像的统一有界性（§8.2 第五步）

状态：finiteness green（hull⊆canonical 紧 → measure_lt_top，S920/S806）；正性走 S1023/S923 开集路线（编译中）。
剩余：
- P4-A：paperFaithfulThetaHull 正测度收尾（Mzk1PaperFaithfulHullActual）。
- P4-B：块级 paper 目标无条件化（S800 qPilotPaperRegionLog ≤ paperHullLog 的 pos/fin discharge；注意 rootThetaHull 含 j=0 与 NonzeroHull 的口径差异）。
- P4-C：统一容器对“全部允许像”（含 Ind2 μ2l 轨道与 Ind3 输出 hull）成立，而不只是有限子族。

## P5 — 路线三来源检验（§8.2 第六步；§6.2–§6.6）

状态：语义字典 PARTIAL（root-unit 可建、etale theta/Kummer 缺）；C-Divisor C1 partial、C3/C4/C5 BLOCKED（Mathlib 无 order-at-O/WeilDivisor/principal divisor API）；仿射 order 基础设施 partial（缺 IsIntegrallyClosed）；C-Theta 乘法移位 green、一般 Z±P 缺线丛平凡化；C-Phase 判定完成（独立相位 iff 2l|a_j；2l 幂代价）。
剩余：
- P5-A：analytic oddTheta ↔ root-valued paper theta 的实际识别（C-Theta 唯一缺口；含 label 索引 shift）——高难，先做可行性/精确缺口。
- P5-B：仿射 order 补 IsIntegrallyClosed（正则局部环→正规），然后 orderAtAffine + fP 零点阶 1，再向 C3 推进。
- P5-C：C-Phase 消费：把 label-indexed 相位族与 C-Theta 比值等变性接起来（依赖 P5-A）。
- P5-D：C-Norm 的 (C13) 剩余（Galois 不变性小引理）与 (C18) restriction-of-scalars 实例化。
停止条件：来源不一致、只得到主除子零 degree、或全部难度留在未控常数。

## P6 — 全局范数/比较态射（§8.2 第七步；§6.10 (C17)–(C20)）

状态：(C13)/(C15)/(C16) green；product formula + Arakelov degree 接口 green；q 侧 degree 条件桥 green；place map + 逐位 valuation + 单 place ExplicitDivisor + 全 bad 求和 green；B4/B5 条件核心 green。
剩余：
- P6-A：(C17) 的实际实例化：把 q/Θ 两个行列式线接到 WeightedDeterminantPacket（见 coord/P6-WEIGHTED-DET-PACKET-PLAN.md，标注为 HANDOFF §8.2 P6 的实例化路径）并证 weighted 差 = N·M。
- P6-B：GAP-DET-HAAR（一般 B∈GL_d(Q_p) 的矩阵 SNF/|det|_p Haar 缩放；受限 Q_p^n 基础已在 Mzk1MatrixHaarBaseActual 起头）+ GAP-DUAL-TRANSPOSE + GAP-QVFAM。
- P6-C：GAP-SOURCE-NATIVE-Q general（index map/逐位几何构造）；GAP-NORM-ARCH（arch 进入 degree）。
- P6-D：(C20) 的 arch 估计（当前不可达，先写缺口）。
停止条件：需要把“足够小截面存在”当外加假设，或把局部场同构伪装成全局态射。

## P7 — 完整目标组合与验收（§8.2 第八步）

状态：不可达；当前只有组件级 green 与 gate 盘点（coord/GATE-STATUS-R29.md）。
剩余：
- P7-A：每轮更新 gate 状态与 AUDIT_LEDGER；对新增 green 做 vacuous/循环/隐藏假设审计（coord/R29-GREEN-AUDIT.md 模板）。
- P7-B：最终 assembly comparator + 公理闭包（仅登记缺口，不声称）。
只有 P0–P6 全部满足才报告 target_accepted。

## 认领规则

- 挑一项，在回报里写清 P 编号与 § 引用；完成后更新对应 coord 文档与 AUDIT_LEDGER。
- 不改题/不新增假设换 green、无 sorry/axiom、lana 只参考；新文件路径报 Lead 加 watchdog 名单。
- 符合停止条件的局部结论照实记录“该机制不足/该候选停止”，不要包装成进展。
