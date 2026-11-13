# P1-MULTIFACTOR-BLOCK — 多因子 p-adic 张量块预备勘察（task-87）

日期：2026-11-13（Aisa/Shanghai）。**只读勘察，不编辑、不编译**（统一 watchdog 约定）。

## 0. 范围

目标：为 task-87 的 P1（构造多因子真实张量块 + 实际 Ind1 张量重排 + 生成矩阵 G/满秩）与 P2（同一 G 的路线一/二联合诊断）列出**可用真实对象、精确 file:line、olean 状态与缺口**。以下对象均在当前 checkout 内实际存在，未用 toy/PUnit/True 替代。

## 1. 可用真实对象

| 对象 | file:line | size / olean | 事实 |
|---|---|---|---|
| `ArithmeticTensorTupleBlock places tuple` | LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceArithmeticTensorBlocks.lean:26 | olean 待核 | `FinitePadicTensor (p:=p) (fun i => CommonPrimeCompletion (places i (tuple i)))`；多因子（ι 有限）按 tuple 的 p-adic 张量块；`arithmeticTensorTupleLogRegion`、`isCompact_*`、`finrank_*` 同文件 |
| `ArithmeticPacketTensor places` + blocks 等价 | 同文件 L29–L39 | — | `arithmeticTensorBlocksAlgEquiv` 与 `...ContinuousLinearEquiv`；块投影 `arithmeticTensorTupleProjection` |
| `tensorIntegerLattice` | LeanFormal/IUT/Foundations/LocalFields/FinitePadicIntegerTensorLattice.lean:46 | OLEAN 403,440B | `Submodule ℤ_[p] (FinitePadicTensor p A)`；`isCompact`/`isOpen`/`Module.Finite`/`Module.Free` + `padic_span_...=⊤`（满格） |
| `integerTensorToPadicTensor` / `integerTensorEquivLattice` | 同文件 L71/L85 | — | 整数张量 → p-adic 张量；自由格与张量块等价的入口 |
| `arithmeticTupleValuationIntegerLattice` | LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIntegerTensorComparison.lean:32 | OLEAN 322,624B | **定义为** `tensorIntegerLattice (A := CommonPrimeCompletion...)`；即 `R := arithmeticTupleValuationIntegerLattice`（:32-35） |
| `ArithmeticTupleValuationIntegerTensor` | 同文件 L37 | — | `PiTensorProduct ℤ_[p] (fun i => valuationIntegerLattice ...)`；`...ToBlock` 注入（L42–L53），可用于“整数张量 ↔ 块” |
| `arithmeticTupleValuationIntegerQpBasis` | IntegralTraceDualTensorInclusion.lean:293 | OLEAN 1,728,800B | 块的实际 Qp 基；L328 `..._eq_piTensorProduct` |
| 局部/整体 trace form 非退化、双对偶基 | 同文件 L333/L338/L346/L352 | — | `arithmeticTupleLocalTraceForm_nondegenerate`、`...DualQpBasis`、`...Lattice_eq_basisIntegralLattice`（路线二 S 的现成入口） |
| `arithmeticTupleLogTensorIntersectionIndex` / `arithmeticTupleHolomorphicIntersectionIndex` / `arithmeticTupleLogTensorUnitLogVolume` | FinitePlaceIntegralTensorCovolume.lean:75/79/92 | OLEAN 432,248B | 实际交指数与对数体积；`...UnitLogVolume_eq_relativeHaarLog`（L128）/`le_hull`（L143）/`eq_fieldLogVolume`（L157） |
| `PrcAutomorphismTensorAction` | tmp/sheaf/xif/paper/Ind1AutomorphismTensorActionActual.lean:44 | OLEAN 85,216B | `ActualTensorPacket C j vQ ≃ₗ[Real] (⨂[Real] i, DirectSumFactor ...)` = `PiTensorProduct.reindex`；**当前是 Real 载体，不是 p-adic/整数格** |
| `PrcAutomorphism` / `Ind1TensorAction` / `ActualTensorPacket` | tmp/sheaf/xif/paper/MultiradialProcessionActual.lean:70/96/102 | OLEAN 277,016B | capsule-level 实际 Ind1 张量重排；`ActualTensorPacket = TensorPacket (logShell j) vQ` |
| `productIntegerLattice` / `productHullLattice` | LeanFormal/IUT/Foundations/LocalFields/ProductIntegerLattice.lean:26/65 | OLEAN 156,848B | 有限积局部域的 `ℤ_[p]`-整格与 hull；`isCompact/isOpen`（Finite J, ProperSpace）；可作为多因子整数格/Hull 的参照 |

## 2. P1 构造草图（基于上述对象）

1. 取有限坏位索引 `ι`（如 n 个坏位 `b_1..b_n`），用 `places : (i:ι) → V i → FinitePlaceAtPrime K p` 与 tuple `(tuple i)` 选每个因子的局部完备化；块 `E := ArithmeticTensorTupleBlock places tuple`（多因子 `FinitePadicTensor`，同一 p）。
2. 整数格：`L0 := arithmeticTupleValuationIntegerLattice places tuple = tensorIntegerLattice`（已 compact/open/free/满格）；`O_E` 用 `IntegralTraceDualTensorInclusion` 的整闭包/对偶基；`R` 与 `O_E` 都在现有文件中有实际定义。
3. G：用 `arithmeticTupleValuationIntegerQpBasis` 取 `L0` 的 `ℤ_[p]`-基，对每个合法像取 `O_E`-生成元，写列 → `G`。
4. Ind1：现有 `PrcAutomorphismTensorAction` 是 `PiTensorProduct.reindex`（Real 载体）；**需把它落到 `FinitePadicTensor`/`tensorIntegerLattice`**（或证明实际作用与 reindex 在块/整数格上的交换），这一步是 P1 的主要新证明。
5. S/路线二：用 `arithmeticTupleLocalTraceForm_nondegenerate` + 双对偶基 `arithmeticTupleValuationIntegerDualQpBasis` 组装迹矩阵 S；交格 `X_G={x : Gᵀ S x ∈ ℤ_p^r}` 的准入由 `IntegralTraceDualTensorInclusion` 提供。

## 3. 缺口/阻塞（P1 前必须解决）

1. **多因子不同 valuation / 不同 p**：`FinitePadicTensor (p:=p)` 固定 p；若 b_i 属于不同 p（不同剩余特征），不能直接共用一个 `FinitePadicTensor`——需分别构造 p-adic 块后做有限积（或明确只取同一 p 的多个坏位）。**UNKNOWN**：现有仓库是否有跨 p 的实际张量块；本次未发现现成构造。
2. **Ind1 在 p-adic/整数格的实现**：`PrcAutomorphismTensorAction` 仅在 `Real` 载体上；到 `ArithmeticTensorTupleBlock`/`tensorIntegerLattice` 的 reindex 交换性与整性**未构造**（关键缺口）。
3. **G 的满秩证明**：Qp 基与像生成元可写，但没有现成“G 满行秩”定理；需用 `Module.finrank`/`Submodule.span`/SNF 证明。
4. **route1 工具不完整**：task-77 的 A3 全链、A4、A8 Haar 比率仍 PENDING（见 `coord/ROUTE1-INDEX-TOOL.md`）；route1 指数公式可先用 A2+有限链手工完成，A4/A8 不能声称已证。
5. **route2 交格体积**：迹对偶基/非退化已有，但“同一 G 的 X_G 相对体积”与 route1 指数的交叉核对尚未组装；需要同一 Haar 归一化（`arithmeticTupleLogTensorUnitLogVolume_eq_relativeHaarLog` 可作锚点）。
6. **公共标量判定边界**：paper 非零标签族 `paperRootThetaImageNZ=F(c_root)O_hol` 是公共标量族（A8 停止：相对 index 与 m 无关）；`rootThetaHull` 含 j=0 固定分量 `F(0)O_hol=R O_hol`，A8 前提不成立。多因子 G 诊断必须显式区分该零标签/固定分量，否则会把 q-无关项误算成增益（HANDOFF-OBJECT-TABLE §3.2–3.3）。

## 4. 结论（预备）

- P1 可用的真实对象链已齐全到“块 + 整数格 + 迹对偶 + 指数/体积工具”的一层；**真正新工作**是把 Ind1 张量重排落到 p-adic 整数格并证明 G 满秩。
- 若只能取同一 p 的多个坏位，多因子块可实现；跨 p 需另建产品构造（缺口 1）。
- route1/route2 的联合诊断在同一 G/Haar 下可行，但 route1 A3/A4/A8 未闭合，必须先补齐或明确只使用 A2 可证部分。

## 5. 状态

- 本文件为 **P1 预备节（只读勘察）**；未写 Lean、未编译。task-87 的 P1 Lean 文件 `Mzk1MultiFactorBlockActual.lean` 尚未创建。
- 下一步顺序：确认多因子 p 选型（同 p 多坏位）→ 定义块/整数格 → Ind1 reindex 整数格版本 → G/S → 满秩 → P2 联合诊断。

## 6. P1 实体（Lean 文件已写：tmp/sheaf/xif/paper/Mzk1MultiFactorBlockActual.lean）

文件大小 4,431B；命名空间 `LeanFormal.IUT.XiFPaper.Mzk1MultiFactorBlockActual`；**只使用真实对象**（无 toy/PUnit/True/sorry/axiom）。

| 声明 | 内容 | 依赖/来源 |
|---|---|---|
| `MultiFactorBlock` | `ArithmeticTensorTupleBlock places tuple`（多因子 `FinitePadicTensor`） | FinitePlaceArithmeticTensorBlocks.lean:26 |
| `MultiFactorIntegerLattice` | `arithmeticTupleValuationIntegerLattice places tuple` = `tensorIntegerLattice` | FinitePlaceIntegerTensorComparison.lean:32 |
| `MultiFactorLogRegion` | `arithmeticTensorTupleLogRegion places tuple` | FinitePlaceArithmeticTensorBlocks.lean:61 |
| `multiFactorIntegerLattice_compact/_open/_span_top/_free` | 紧/开/满格/自由（实际整数格） | 同文件 L75/L81/L87 + FinitePadicIntegerTensorLattice L52/L58/L62 |
| `multiFactorLogRegion_compact` | 实际 log-shell 张量区域紧 | FinitePlaceArithmeticTensorBlocks.lean:71 |
| `multiFactorQpBasis` | 实际 Qp 基（局部整基张量） | IntegralTraceDualTensorInclusion.lean:293 |
| `multiFactorDualQpBasis` | 实际迹对偶 Qp 基 | 同文件 L346 |
| `multiFactorLocalTraceForm_nondegenerate` | 每个因子的局部迹型非退化 | 同文件 L333 |
| `factorPermutationBlockEquiv σ` | 实际 p-adic 块上的因子置换 `PiTensorProduct.reindex`（ℚ_[p]），到置换后的 tuple 块 | PiTensorProduct.reindex |

状态：**PENDING-WATCHDOG**（文件在 `dag/watchdog/extra-targets.txt`，尚无 START/DONE/FAIL，olean 不存在）。

## 7. P2 联合诊断设计（同一 G/S + 同一 Haar）

### 7.1 生成矩阵 G 的列

固定 `L0 := MultiFactorIntegerLattice places tuple`，取 `multiFactorQpBasis`（局部整基的张量）限制到块；对有限合法像族 `g ∈ G acts`，用 `factorPermutationBlockEquiv`（或实际 Ind1 的 p-adic 重排）取 `g(L0)` 的列；以 `L0` 的 `ℤ_[p]`-基 + 各像的 `O_E`-生成元为列得 `G ∈ M_{d×r}(ℚ_[p])`（`d = finrank`）。清分母 `A = p^k G` 后，Smith 初等因子 `p^{t_a}` 给 `log(μ(Gℤ_p^r)/μ(ℤ_p^d)) = (kd − Σ t_a) log p`（HANDOFF §4.5 的 A5/A6）。

### 7.2 路线一（有限商指数）

链 `L_i = L_{i-1}+B_i`（`B_i = g_i(L0)`）；`C_i = L_i/L_{i-1} ≅ B_i/(B_i∩L_{i-1})`（A1，task-77 green）；index `#C_i = latticeIndex L_{i-1} L_i`（A2）；`λ(L_r)−λ(L_0) = (1/d)Σlog#C_i`（A3 全链，task-77 仍 PENDING，需补齐或先用 A2 逐步算）。

### 7.3 路线二（迹对偶交格）

用 `multiFactorDualQpBasis` 与局部迹型非退化（`multiFactorLocalTraceForm_nondegenerate`）组装全局迹矩阵 `S`；交格 `X_G = {x : Gᵀ S x ∈ ℤ_p^r}`；相对体积用同一 Haar 归一化（`arithmeticTupleLogTensorUnitLogVolume_eq_relativeHaarLog`，FinitePlaceIntegralTensorCovolume:128）计算。

### 7.4 交叉核对与判定

- 交叉核对：同一 `G`、同一 Haar 下，路线一的 `Σlog#C_i` 与路线二的相对体积必须一致；不能各造一份增益；
- 判定因子置换/不同 valuation 是否打破公共标量：检查所有像的生成矩阵列是否都是同一个 p-标量倍（`c_root` 型）；若是 → 公共标量停止（相对 index 与 m 无关，无 m 线性相对增益）；若出现非公共方向（如因子置换混合不同 q_v 权重）→ 记录非平凡指数/体积差及 m 依赖；
- 若仍无增益：按 HANDOFF §8.2 P2 停止条件精确记录原因（G 的列全在同一标量线上/整数格未被作用扩展），转来源/全局（P5）。

## 8. 当前缺口（P1/P2 推进前必须补）

1. **实际 Ind1 → p-adic 整数格**：`factorPermutationBlockEquiv` 是块级 reindex（ℚ_[p]），但尚未证明它就是来源 Ind1 `PrcAutomorphismTensorAction`（后者在 Real 载体）经实际张量重排的对应；整数格 `L0` 的保持性需证明；
2. **G 的满秩**：`multiFactorQpBasis`/像列可写，但满行秩未证（需 SNF/span/finrank 论证）；
3. **S 的组装**：局部迹型非退化已有，全局 `S` 与 `X_G` 体积公式未组装；
4. **route1 A3 全链/A4/A8 Haar 比率**：task-77 仍 PENDING（见 `coord/ROUTE1-INDEX-TOOL.md §7`）；
5. **跨 p 情形**：当前 `FinitePadicTensor` 固定 p；不同 p 的坏位需另建有限积构造（未发现现成对象）；
6. **零标签/固定分量**：若诊断对象是 `rootThetaHull`（含 j=0），必须拆出 `F(0)·O_hol=R·O_hol` 的 q-无关分量，否则会把固定项误算为增益（HANDOFF-OBJECT-TABLE §3.2–3.3）。

## 9. 下一步顺序

1. 等 watchdog 对 `Mzk1MultiFactorBlockActual.lean` 的 DONE/FAIL；若 FAIL 读 per-file log 修；
2. 用 `factorPermutationBlockEquiv` 定义有限像族及 `G`（实际列），证明块/格保持；
3. 证明满秩（SNF/span）；组装 `S`/`X_G`；
4. 补齐 task-77 的 A3 全链/A4/A8 比率后，跑 P2 联合诊断并写判定；
5. 判定无增益则按 §8.2 P2 停止条件记录并转来源/全局。

## 10. Build 证据（P1 实体）

- `Mzk1MultiFactorBlockActual.lean`：**DONE EXIT=0 @2026-11-12T20:41:34Z（47s）**（retry after 20:37:39 FAIL；修复 namespace open + 同步置换 places/tuple）；
- olean：`.lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1MultiFactorBlockActual.olean`，**88504B**，mtime 2026-11-12T20:41:34.322Z；
- 无 sorry/axiom；linter 仅有 unusedSectionVars warning（不影响编译）。

## 11. P2 进展与判定（task-87，20:51:52Z 后）

### 11.1 Build 证据

- `Mzk1MultiFactorBlockActual.lean`：**DONE EXIT=0 @2026-11-12T20:51:52Z（32s）**；olean 214288B，mtime 2026-11-12T20:51:52.498Z；无 sorry/axiom（仅 unusedSectionVars warnings）。

### 11.2 G 的行满秩（当前到哪一步）

- **已证**：`generatedLattice_full`（`MultiFactorIntegerLattice ⊔ ⨆ images` 的 `ℚ_[p]`-span = ⊤）。这是 lattice-level 满格；由 `L0` 的满格性继承，不依赖 Ind1 矩阵。
- **未证**：`generatorMatrix` 的**矩阵行满秩**。两个具体缺口：
  1. 当前 `generatorMatrix` 的列索引只有 `L0整基索引 × G`（像 g(b_j)），**没有包含 L0 自身的基列**；要证“列张成整个块”必须把列索引扩为 `Option G × L0整基索引`（none=L0 基列，some g=像列）。
  2. 矩阵行列式/秩的 API 未接：需用 `Module.Basis`/`Matrix.det`/`finrank` 证明方阵行列式非零，或直接用 `Submodule.span` 与 `finrank` 证列张成；这与 lattice-level 满格是两个不同断言。
  计划：先改列索引为 `Option G × L0BasisIndex`，再用“L0 基列的 ℚ_[p]-span = ⊤”直接证列张成（不需要 SNF）；SNF 只用于**指数/体积值**，不是满秩本身。

### 11.3 S / X_G 交格相对体积

- 已有实际构件：`multiFactorDualQpBasis`（实际迹对偶 Qp 基）、`multiFactorLocalTraceForm_nondegenerate`（局部迹型非退化）、`arithmeticTupleValuationIntegerDualQpBasis`（整体对偶基，IntegralTraceDualTensorInclusion:346）；`arithmeticTupleLogTensorUnitLogVolume_eq_relativeHaarLog`（FinitePlaceIntegralTensorCovolume:128）给同一 Haar 归一化。
- 设计（待写 Lean）：迹矩阵 `S_{k l} = Tr(g_k(b_l))`（g 为有限像族、b 为 L0 整基）；`X_G = {x : Gᵀ S x ∈ ℤ_p^r}`；相对体积按 A2/A3 的同一 Haar 计算；与路线一有限商指数 `#C_i` 交叉核对。
- **缺口**：S 的全局矩阵与 X_G 的显式定义/体积公式尚未写；route1 A3 全链/A4/A8 比率仍未闭合（task-77 remaining gaps），因此“同一相对体积”的交叉核对目前**未完成**。

### 11.4 因子置换/不同 valuation 是否打破公共标量（判定）

- 现有 `factorPermutationBlockEquiv σ` 只是**块级 `PiTensorProduct.reindex`**（ℚ_[p]，places/tuple 同步置换）；它是张量因子置换，不自动等于来源 Ind1 的实际 p-adic 作用，也尚未证明保持 `MultiFactorIntegerLattice`（整数格保持性未证）。
- 若像族只是公共标量 `c_i · L0`：A8 停止引理适用（相对 index/体积比与标量无关；paperRootThetaImageNZ 的非零标签族即此型）⇒ **无 m 线性相对增益**；`rootThetaHull` 含 j=0 的 `F(0)O_hol=R O_hol` 固定分量，公共标量前提不成立（HANDOFF-OBJECT-TABLE §3.2）。
- 若像族包含非公共方向（因子置换混合不同 q_v 权重）：可能产生非平凡指数/体积差；但**当前尚未构造实际 Ind1→p-adic 整数格映射与 G 值**，因此“是否打破公共标量”目前判为 **UNKNOWN（P2 未决）**，不能声称有增益。
- 判定规则：先完成 11.2 列张成/满秩 + 11.3 的 S/X_G；若 G 的所有列在同一 p-标量线上 → 公共标量停止（记录 §8.2 P2 停止条件）；若出现非公共方向 → 记录具体指数/体积与 m 依赖，再进 A-Estimate/B-Estimate。

### 11.5 结论（当前可报告）

- P1 foundation + P2 lattice-level 满格 green（file:line 见 §6/§10；20:51:52Z DONE）。
- 矩阵行满秩、S/X_G、route1/route2 联合诊断**尚未完成**；当前不能断言非平凡 m 增益，按 §8.2 P2 尚处于“继续构造/诊断”而非“停止”。

### 11.6 更新（21:22:36Z）：G 列张成/满秩已证

- `Mzk1MultiFactorBlockActual.lean` **DONE EXIT=0 @21:22:36Z（33s）**；olean 326392B，mtime 2026-11-12T21:22:35.748Z。
- 新增并 green：
  - `integerBasis`：`L0` 的 `ℤ_[p]`-基；
  - `integerBasis_span_top`：该整基的 `ℚ_[p]`-span = ⊤；
  - `generatorColumn` / `generatorColumn_span_top`：**完整列族（L0 基列 + 有限像列）的 `ℚ_[p]`-span = ⊤**（矩阵行满秩的向量形式；L0 列已足以张成）；
  - `fullGeneratorMatrix`：完整列族在 `multiFactorQpBasis` 下的实际坐标矩阵。
- 这解决了 §11.2 的缺口 1/2（列缺 L0、列张成）；**矩阵行列式/SNF 数值**仍未写（SNF 只用于指数/体积值，不是满秩本身）。


## 12. task-87 收尾（2026-11-13 14:44Z）

- #7 THETA-DEG：全收口（P7ThetaDeg/B2/C3/Weight/Cancel 全 DONE）。
- B4：**DONE（14:44:03Z）**——`Mzk1CanonicalDiagUncondFinalActual` 无条件 `canonical_diag_volume_ratio_uncond`（olean 216,480B），绕开 diagHomeo image bridge。
- task-87 的 P1/P2 预备与 X_G/对角双链均已收口；剩余为其他 lane 的 Ind1/一般 X_G 语义桥（不在本 lane 活动范围）。
