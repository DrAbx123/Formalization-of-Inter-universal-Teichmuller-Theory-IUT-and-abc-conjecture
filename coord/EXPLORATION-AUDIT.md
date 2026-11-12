# EXPLORATION-AUDIT — 探索路线交付模板与合规审计规则（A918）

日期：2026-11-12（stage4）。依据：`coord/EXPLORATION-ROUTES.md`（v2）。**本文件只定规则与审计，不改任何产出文件。**

## 1. 四节交付模板（强制）

每个阶段产出一个 `coord/EXPLORATION-<路线>-<阶段>.md`，且**必须**包含：

### 1.1 文件头（强制字段）

| 字段 | 要求 |
|---|---|
| `Status` | 显式状态行，只能取：`MODEL`（模型/接口，非定理）、`NUMERIC`（数值数据，非定理）、`PROVED`（仅限 Lean 文件 + olean + trio gate）、`LITERATURE`（外部文献输入，须登记）、`STOP`（停在判定点，写负结果）、`PARTIAL`（未过判定点） |
| 路线/阶段 | 例：“路线 C，阶段 C1” |
| 日期/作者 | 例：2026-11-12；lane 名 |
| 版本钉住 | lana 引用只能 `Iut/...` 根树 + 行号（A896 规则，见 `EVIDENCE-ISOLATION-REGISTRY.md` §7）；数值工具版本（Sage/Python 等）与命令；Lean 文件需给出 EXIT/olean/trio |

### 1.2 四节（缺一即不合规）

1. **做了什么**：输入/命令/脚本路径/工具版本；读了哪些只读源（根树 file:line）；产出了哪些机器文件（含 EXIT/olean/trio 或 CSV/JSON 路径）；不允许“我算了一下”式描述。
2. **数据表**：全部数值/模型表；每行/每表标 `NUMERIC` 或 `MODEL` 或 `PROVED`；样本量、筛选条件（如 admissible 过滤）、剔除规则必须写明；可复现（脚本+命令+数据文件路径）。
3. **与判定条件的对照**：逐条对照 `EXPLORATION-ROUTES.md` 该阶段“判定（有戏）/（停）”；必须给出**明确判定**：PASS / PARTIAL / STOP；不能用“有希望”“差不多了”替代。
4. **下一步或停止**：若 PASS/PARTIAL，列不超过 3 条具体下一步（含 owner 与判定点）；若 STOP，写负结果（“没有信号”，不包装成进展）。

### 1.3 禁止项

- 把 `MODEL`/`NUMERIC` 写成 `PROVED` 或“定理”；零违例 ⇒ 只能说“样本内无反例”；
- 用缺失 olean 的 lana 声明当 green（只能标 `LITERATURE/UNVERIFIED` 或 `GAP`）；
- 手工调系数后当定理；省略样本筛选/剔除；
- 引用 `tmp/sheaf/lana*` 等旧副本的行号（A896：一律根 `Iut/`）；
- 把探索文档写入最终证据链（探索产出永不进 `EVIDENCE-ISOLATION-REGISTRY` §1 的 green 计数）。

## 2. 试金石（3^k−1）必答项

每个**新主张**（不是每个数据文件）都必须回答以下四问，写入交付文档 §1 或 §3：

1. **Q1 量词范围**：主张是全称不等式、有限样本、还是条件陈述（写明条件）；
2. **Q2 信息入口**：`3^k − 1` 不是近似完全幂”这一信息从哪一步进入？（例如：半径之积、证书多项式的取值、高度比较的某一步、或明确“本阶段不使用，只作为下游 A3/B1/C3 的输入”）；
3. **Q3 丢失检验**：若去掉该信息，主张退化成什么更弱的陈述？（若答不出，说明主张没有用到试金石 ⇒ 可能只是换说法）；
4. **Q4 判停**：答不出 Q2/Q3 ⇒ 该主张 **STOP-NO-TOUCHSTONE**，不得继续立项。

模板句式：

> 试金石：本主张的量词范围是 <…>；`3^k−1` 信息从 <具体步骤> 进入；去掉该信息后主张退化为 <较弱陈述>；因此该主张 <有效/是换说法>。

纯数据阶段（C1/B0/C2）可写：“本阶段不主张不等式；试金石仅在其数据被 A3/B1/C3 定理化时适用，届时在相应主张中回答。”——但**必须显式写**，不能省略。

## 3. 数值 vs 定理标注规则

| 标签 | 含义 | 证据要求 |
|---|---|---|
| `PROVED` | Lean 定理 | 文件 + 我们的 toolchain 编译 EXIT=0 + olean 新鲜 + `#print axioms` 仅 `[propext, Classical.choice, Quot.sound]`；三者缺一不可 |
| `MODEL` | 模型/接口定义（可为 Lean 代码，但只是模型对象） | 文件头明示 MODEL；不得声称对应 IUT/论文对象；允许 trio（仅说明定义不引入公理） |
| `NUMERIC` | 数值数据/拟合/搜索 | 脚本+命令+数据文件+样本说明；零违例只说“样本内无反例” |
| `LITERATURE` | 外部已发表定理 | 按 §4 登记（含 DOI/arXiv、定理编号、假设、验证级别）；只能作显式假设 |
| `UNVERIFIED` | 未核对项 | 不得作为任何结论依据 |
| `STOP` | 判定点停止 | 写负结果与理由 |

补充规则：

- 任何“整性”主张（系数整数、分母素因子受限）必须有证明或文献出处（ROUTES §0.3-3）；
- 拟合关系必须给出函数形式、参数、残差、留出集；不得手工凑整；
- 数值表的样本筛选（admissible 条件、坏位剩余特征、etc.）必须与 ROUTES 规则一致；**有意偏离必须登记**（见 §6 C1 的 p=2,3 案例）。

## 4. 外部假设登记规则

外部定理/外部计算工具一律登记到交付文档 §2 或 §3 的表，格式：

| 字段 | 要求 |
|---|---|
| EID | 唯一编号（如 EXT-C1-1） |
| 陈述 | 逐字或明确标注“ paraphrased”；含量词与假设 |
| 来源 | lana：根 `Iut/...:line`（A896 规则）；文献：作者/标题/期刊或 arXiv/DOI/定理编号+页码 |
| 验证级别 | V0=仅书目元数据；V1=已读陈述；V2=陈述+假设逐字核对；V3=仓库内形式化（trio） |
| 状态 | `NAMED`（采用为输入）/`UNVERIFIED`/`REFUTED` |
| 消费者 | 哪个 Lean 文件/条件定理会把它作为显式假设 |
| 公理闭包 | 必须不在 trio 内（显式假设）；不得写成 `axiom`/`sorry` |

规则：

- 外部定理只能出现在 Lean 中作为显式条件（例如 `MestreOesterleBound : Prop`），不得进最终公理闭包；
- 未登记的外部定理出现在任何结论链 ⇒ 审计 FAIL；
- 计算工具（Sage/Cremona/sympow/LMFDB）也要登记为“外部计算来源”，注明版本与输出文件；
- 文献无法读取正文时只能标 `UNVERIFIED`（V0/V1），不得作为判定依据（参考 E7 审计 `coord/E7-SOURCE-AUDIT.md`）。


## 5. 每个判定点的通过/停止条件

（判定点来自 `EXPLORATION-ROUTES.md`；审计要求：交付文档必须写出本表对应行的判定结果。）

| 阶段 | 通过（有戏） | 停止 |
|---|---|---|
| A0 | 原文定理逐字转述 + 计算量清单；陈述无疑义 | 陈述拿不准 ⇒ 停，不许凭印象继续 |
| A1 | 用原文例子复现上界，三个数（共形半径/增长积分/上界）与原文对上 | 对不上 ⇒ 修管线；修不好停 |
| A2 | 至少一族“半径之积 > 1”（某参数区间、同一整体坐标、分歧/分母全计入） | 所有族半径之积 ≤ 1 ⇒ 停 |
| A3 | 得到 `log c ≤ C·log rad + cost(m)`，且 `cost(m)` 不随 k 线性增长 | `cost(m)` 吃掉全部增益或半径之积无法 >1 ⇒ 停 |
| B0 | 对 N≤500 全半稳定曲线，`r_f` 与数据库 `deg φ` 一致核对表 | 不一致且无法解释 ⇒ 停 |
| B1 | 最优证书的最大素数/次数随 N 至多 `(log N)^k` 增长，且出现构造规律 | 复杂度随 N 多项式增长且无规律 ⇒ 停 |
| B2 | 显式构造 `P_N,f` 在全样本验证 `r_f | P(f)` 且 `|P(f)| ≤ N^C`，新引理逐条过试金石 | 任一失败 ⇒ 停 |
| C0 | Ind2 公式证出或否掉 + archDefect 精确值；两条都有结论 | 只有模型层 ⇒ **C0 未通过**（计算器不能叫“精确”） |
| C1 | 计算器 + ≥20 条手算曲线核对一致；admissibility 已实现；偏离规则已登记 | 核对不一致/缺 exactness ⇒ PARTIAL |
| C2 | 不变量库按 ROUTES 清单齐全（导子、判别式、deg φ、Tamagawa、挠、Ш 解析阶、实周期、同源类、a_p、v_p(Δ)、小 ℓ 挠域数据） | 字段缺失/来源不明 ⇒ PARTIAL |
| C3 | 剔除已知等价关系后仍有全样本零违例关系；样本量/族已声明 | 只剩已知等价关系 ⇒ 停 |
| C4 | 零违例关系 + X 有已知上界或可独立证明 ⇒ 写成猜想并过试金石 | 无法证明 X/过不了试金石 ⇒ 停 |

## 6. 已落盘文件合规审计（快照 2026-11-12T10:52Z 附近；注意 c2 有并发写入）

### 6.1 审计结果总表

| 文件/产物 | 四节 | 状态标注 | 试金石 | 外部登记 | 树根钉住 | 判定/停止 | 结论 |
|---|---|---|---|---|---|---|---|
| `coord/EXPLORATION-C-C0.md` | ✅（1 What was done / 2 Data table / 3 Comparison / 4 Next step） | ⚠ 无显式 Status 行（§3 只说“停在判定点”） | ❌ 未答 | ⚠ 无外部定理（lana gap 属内部依赖）；未列 gap 登记表 | ✅ “root tree” + Gap L66/L459/L463（实测有效） | ⚠ §4 有下一步，但未写明确 `C0 PASS/PARTIAL/STOP` | **基本合规；需补 Status/试金石/明确判定** |
| `coord/EXPLORATION-C-C1.md` | ✅（1 做了什么 / 2 数据表 / 3 对照 / 4 下一步/停止） | ✅ 文件头 Status: model calculator + “NOT a proof” | ❌ 未答（数据阶段可写“试金石仅未来定理化适用”，但未写） | ⚠ `hullPacket_tame` 未给根树行号（应 `Iut/WallEquiv/VcI.lean:844`）；Sage/e=p^cond 模型估计未登记；p=2,3 偏离 ROUTES 规则 4 已述未登记 | ⚠ 名称引用无 file:line | ✅ §4 “Stop point: no signal claim” | **基本合规；需补试金石/外部登记/行号/偏离记录** |
| `coord/EXPLORATION-B-B0.md`（本轮新落盘） | ✅（1 做了什么 / 2 数据表 / 3 与 B0 判定条件对照 / 4 下一步） | ⚠ “不写 Lean；仅数据与脚本”但无 `NUMERIC` 标签行 | ❌ 未答（B0 数据阶段可声明） | ⚠ 隐含使用 Agashe–Ribet–Stein 定理，未按 §4 登记（需引用+定理编号）；SageMath 10.9/Cremona/sympow 未登记为外部计算来源 | N/A（无 lana 引用） | ✅ §3 “判定：B0 基础对象可算，管线成立” | **较好；需补 Status 标签/试金石/外部登记** |
| `b0_*` 原始产物：`tools/b0_modular.sage`、`tmp/b0_probe*.sage`（5 个）、`tmp/b0_run.log`、`coord/b0_modular_data.json`（33KB）、`coord/b0_data.csv`（43 行） | 由 B0 doc 覆盖 ✅ | 日志含 Sage 10.9、命令、errors=0、known_checks | 同 B0 doc | 同 B0 doc | N/A | B0 doc §3 ✅ | **作为 B0 附件合规**；`b0_probe*.sage` 为探索草稿，建议标 scratch（非交付） |
| `c2_*` 产物：`tools/c2_invariants.py`（6KB）、`tools/c2_invariants.sage`（3.1KB）、`data/c2_invariants.json`（40 samples；tamagawa/degφ/Sha/period/isogeny/torsion_full 多为 null 并给出原因字段 ✅ 好实践）、`data/c2_invariants.csv`（4.6KB）、`coord/c2_invariants.csv`（**73.8MB，4155 行**，字段含 tamagawa/modular_degree/torsion——**来源未声明**，疑为另一 lane 的 Cremona dump）、`coord/c2_invariants.jsonl`（**0 字节**） | ❌ **无 `EXPLORATION-C-C2.md`** | ❌ 无标签 | ❌ | ❌ | N/A | ❌ | **不可审计为交付**；C2 未完成（见 6.2） |
| `coord/EXPLORATION-A-A0.md` | 结构可见（1/2.1–2.7 子节） | 未审 | — | — | — | — | 本轮范围外（任务只审 C0/C1/b0/c2）；建议下轮审计 |
| `coord/EXPLORATION-ROUTES.md` | 指导书 | — | — | — | — | — | 非交付物 |

### 6.2 C2 专项发现（需 owner 处理）

- **缺交付文档**：`coord/EXPLORATION-C-C2.md` 不存在；四个 C2 产物无法按模板审计；
- **c2 数据字段不齐**（对照 ROUTES C2 清单）：`data/c2_invariants.json` 中 `tamagawa/deg_phi/analytic_sha_order/real_period/isogeny_class/torsion_full` 均为 null（有原因字段，做法可取，但 C2 按定义未完成）；`conductor_model` 明确为模型值；
- **文件重复/来源不明**：`data/c2_invariants.csv`（4.6KB）与 `coord/c2_invariants.csv`（73.8MB，含 tamagawa/modular_degree）**同名不同内容**；后者 4155 行远多于 C2 的 40 samples，且来源未声明（可能另一 lane 并发产出）；
- **空文件**：`coord/c2_invariants.jsonl` 为 0 字节；
- **并发写入**：审计时 `coord/c2_invariants.csv` mtime 10:51Z 且仍在增长可能（快照前后大小不变但同批文件刚写入）⇒ c2 状态不稳定，不可作为判定依据。


## 7. 需补项清单（按 owner/文件）

### 7.1 `EXPLORATION-C-C0.md`

1. 文件头加 `Status: MODEL/PARTIAL — Ind2/archDefect 模型层已证，精确识别 GAP 未闭合（C0 未通过）`；
2. 加试金石段：本地项不直接使用 `3^k−1` 信息；写“本阶段不主张不等式；试金石将在 C0 结果被用于全局不等式时回答”——但更准确是：C0 是**局部精确性**阶段，明确写“无全局主张”；
3. §3 明确判定：`C0 = PARTIAL`（(a) 公式未导出、(b) archDefect 精确值未形式化）；§4 已列下一步，可保留；
4. 保留根树引用（Gap L66/L459/L463 已实测有效），建议补 `hullPacket_*` 的根树 file:line。

### 7.2 `EXPLORATION-C-C1.md`

1. 补试金石段（同 §7.1 的数据阶段模板句）；
2. 外部登记表：`hullPacket_tame`（根树 `Iut/WallEquiv/VcI.lean:844`，V1）、`SageMath 10.9 + E.local_data`（外部计算来源）、`e ≈ p^(conductor_exp)`（MODEL 估计，明确非定理）；
3. 登记偏离：ROUTES §0.3-4 要求“坏位剩余特征为奇”，样本使用 p=2,3 特处理 ⇒ 写偏离理由、影响（M 被 p=2,3 模型项主导）、后续 exactness 计划；
4. 表格逐行加 `NUMERIC/MODEL` 标签（尤其 p=2,3 与 arch 项）；
5. 引用 `hullPacket_tame/hullPacket_finite` 时给根树行号（VcI.lean:844/806）。

### 7.3 `EXPLORATION-B-B0.md` + `b0_*`

1. 文件头加 `Status: NUMERIC（数据管线），NOT a proof`；
2. 补试金石段（数据阶段声明：本阶段无不等式主张；试金石在 B1/B2 主张时适用）；
3. 外部登记：Agashe–Ribet–Stein（`r_f = deg φ`，N 无平方因子；需给定理编号/DOI，V1/V2）、SageMath 10.9 + Cremona 数据库 + sympow（外部计算来源）；
4. 明确 prototype 范围：NMAX=30（43 曲线）vs ROUTES B0 要求 N≤500 ⇒ 标 PARTIAL 并给扩展计划；
5. `tmp/b0_probe*.sage` 标 scratch（非交付）；`tmp/b0_run.log` 可作为运行记录。

### 7.4 `c2_*`

1. **先写 `coord/EXPLORATION-C-C2.md`**（四节 + Status: PARTIAL/NUMERIC），否则 C2 无法审计；
2. 解决重复命名：确定 canonical 数据文件（建议 `data/c2_invariants.json` 为准，`coord/c2_invariants.csv` 若属另一 lane 必须改名并声明归属；不得同名混用）；
3. 补齐 ROUTES C2 清单字段（Tamagawa、deg φ、Ш 解析阶、实周期、同源类、torsion_full；当前 null 且原因已给 ⇒ 列“未完成项”）；
4. `coord/c2_invariants.jsonl` 0 字节 ⇒ 删除或补内容；`data/c2_invariants.csv` 与 JSON 关系需说明；
5. 外部登记：LMFDB API 不可用（已记录 ✅）⇒ 所有字段来源标注（Sage/Cremona/本地计算）；`conductor_model` 等 MODEL 字段保留标签。

### 7.5 通用（所有探索 lane）

- 每份交付按 §1 模板；没有四节/Status/试金石/外部登记的文档一律视为 `PARTIAL`（不得引用为“已有结论”）；
- 任何 Lean 机器文件（如 C0 的 `Mzk1C0Ind2ArchActual`）的 PROVED 标签必须附 EXIT/olean/trio 证据（C0 已附 EXIT=0/trio，符合）；
- 探索文档不得进入最终证据链（见 `EVIDENCE-ISOLATION-REGISTRY.md`）。

## 8. 审计方法（可复现）

1. 对每个交付文档读全文，核对 §1 模板四节与文件头字段；
2. 对文档中每个 `Iut/...:line` 引用，用根 `Iut/` 树逐行核对（A896 规则；`tmp` 副本行号禁用）；
3. 对每个数值/模型表，检查样本量、筛选规则、脚本/命令、数据文件路径是否存在；
4. 对 `c2_*`/`b0_*` 等并发产物，记录 mtime/size 快照并注明“可能并发写入”；
5. 对 PROVED 标签，检查 Lean 文件/olean 新鲜/`#print axioms` trio（或引用既有 registry 记录）；
6. 对每个主张核对试金石四问（§2）；答不出 ⇒ STOP-NO-TOUCHSTONE。

## 9. 与既有审计的关系

- 版本钉住：遵循 `EVIDENCE-ISOLATION-REGISTRY.md` §7（A896）：lana 引用只用根 `Iut/` 树 + 行号；
- green 定义：遵循 registry §1（仓库内 + 我们 toolchain + trio）；探索文档不改变 green 计数；
- 外部文献：遵循 `coord/E7-SOURCE-AUDIT.md` 的验证级别（V0/V1/V2）与不可靠标注；
- 本文件为探索路线的审计模板与判定记录；与 registry 冲突时以 registry §1/§7 为准。

## 10. 本轮审计结论（摘要）

- C0/C1：结构基本合规，**需补试金石、外部登记、明确判定**；C1 的 p=2,3 偏离须登记；
- B0：本轮新落盘文档结构合规、数据/命令/版本清楚，**需补 Status 标签、试金石、ARS/Sage 外部登记、N≤500 扩展**；
- C2：**未完成/不可审计**（缺交付文档、字段不齐、文件重复且来源不明、空 jsonl、并发写入）；
- A0：存在但不在本轮审计范围（建议下轮）。


---

## 11. A923 附录 A：`EXPLORATION-A-A0.md` / `EXPLORATION-A-A2.md` 合规审计（快照 2026-11-12T10:55Z）

### 11.1 A0（Calegari–Dimitrov–Tang 陈述抄录）

| 检查项 | 结果 | 证据 |
|---|---|---|
| 四节 | ✅ 1 做了什么 / 2 数据表 / 3 与判定条件对照 / 4 下一步或停止 | 标题结构完整 |
| Status | ⚠ 有判定句（A0 判定 = 取得精确陈述，可进入 A1），但未用模板六态标签；应为 `LITERATURE (V2) + A0 PASS` | 文件头 |
| 试金石 | ❌ 未答；A0 无不等式主张，应显式写“本轮无主张，试金石暂缓/不适用”（模板允许 defer，但须写） | 全文无 touchstone 段 |
| 外部登记 | ⚠ 文献引用质量好：arXiv:2109.09040v4、JAMS PDF、DOI/URL + 定理编号/页码 + 讲义互核；但未按 §4 表格式登记（EID/V 级别/消费者），也未标 V2 | §1 与 §2 |
| 版本钉住 | ✅ 文献版本/页码/URL 钉住；工作区落盘路径 `tmp/lit/*` 记录；无 lana 引用 | §1 |
| 结论 | **基本合规（A0 PASS 成立）；需补：Status 标签、试金石 defer 句、E-table（V2 + consumer）** |

### 11.2 A2（候选函数族设计）

| 检查项 | 结果 | 证据 |
|---|---|---|
| 四节 | ✅ 1 做了什么 / 2 数据表 / 3 与判定条件对照 / 4 下一步或停止 | 标题结构完整 |
| Status | ✅ 明确：A2 判定 = 候选 F4 符号满足 >1，进入 A3；但半径积只是假设匹配，不是定理上界充分条件 | 文件头 |
| 试金石 | ❌ 未按四问回答；只在 A3 计划中提到家族 `(1,3^k−1,3^k)`。A2 是设计阶段，应写“本轮无不等式主张；试金石在 A3 主张中回答”，并指出 F4 单独只给常数不等式（非 abc 增益） | 全文无试金石段 |
| 外部登记 | ⚠ 缺 §4 表：A0 的 Theorem 2.0.1/Cor 2.0.5 是输入（应登记为 LITERATURE V2）；仓库 Belyi 对象仅列名字（`Mzk1BelyiCanonicalActual` 等），未给文件/olean/trio 或“非 green”标注 | §1 第 1 条、§2 F4 |
| 版本钉住 | ⚠ lana 无引用（无需钉根树）；但 Belyi 仓库对象未钉文件/版本；A0 引用继承 ✓ | §2 F4 |
| 判定/停止 | ✅ §3 明确 F1 不通过 / F2 条件性 / F3 不通过 / F4 通过；§4 列 A3 实验与停止条件（若 m 总 ≤ 上界 ⇒ 全停） |
| 结论 | **基本合规；需补：试金石 defer 句、外部登记表（A0 两定理 + Belyi 对象来源/状态）、Belyi 对象版本钉住** |

### 11.3 C0/C1/B0 补项复核（A923 第③项）

| 文件 | 上轮需补 | 现在（快照） | 判定 |
|---|---|---|---|
| `EXPLORATION-C-C0.md` | Status/试金石/明确判定 | **已补**：§5 有 `Status: PARTIAL`、touchstone defer 答案、`C0 = PARTIAL 停在该判定点`、E-class 登记 E-C0-1..3 | ✅ 完成（建议把 E-C0-* 标注为内部 gap 而非外部文献假设，避免与 §4 外部登记混淆） |
| `EXPLORATION-C-C1.md` | 试金石/外部登记/根树行号/p=2,3 偏离 | **未补**（mtime 未变；无试金石/E-C1 表/`VcI.lean:844`；p=2,3 偏离仍只在正文提及） | ⏳ PARTIAL，待 hull |
| `EXPLORATION-B-B0.md` | Status 标签/试金石/ARS+Sage 外部登记 | **未补**（无模板 Status 行、无试金石段、无 E-B0 表；ARS/Sage/Cremona/sympow 仍未登记） | ⏳ PARTIAL，待 qpilot |


---

## 12. A923 附录 B：A3 交付清单（强制字段）

路线 A 阶段 A3（第一次实验）的交付：`coord/EXPLORATION-A-A3.md`，除 §1 四节与文件头外，**必须逐项包含**：

### 12.1 映射定义（每族一份）

- `p(x) ∈ Q(x)∖Q`、`x(t) ∈ t + t²Q[[t]]`、`φ : D(0,1) → C`（`φ(0)=0`, `|φ′(0)|>1`）、
  `f_1,…,f_m ∈ Q[[x]]` 的**显式表达式**；
- 与三元组 `(a,b,c)` 的依赖：`u = a/c`、坏素数集 `S`、`p(x)` 的选取（如 `x^N`）、
  `x(t)=λ/16` 或 Belyi 覆盖的复合方式；参数区间/分支选择；
- Theorem 2.0.1 假设逐条核对表：`p` 在 `x=0` 无极点、`x*p ∈ Z[[t]]`、`φ*p ∈ O(D)`、
  `x*f_i ∈ Z[[t]]`、`φ*f_i ∈ O(D)`、分母类型 `R=Z` 或 `R=Z[1/N]`（后者须作显式假设）；
- 同一**整体坐标**声明（ROUTES A.5）：所有半径在同一坐标下计算，不得各位各用各的坐标。

### 12.2 `m` 的选择规则

- 候选函数族的构造算法：`f_i` 如何生成（Legendre、代数分支、乘积/导数、Belyi 拉回），
  去重规则、`i` 的取值范围；
- `m` 的**定义**：`Q(p(x))` 上线性无关的函数个数；给出线性无关性判定方法（符号秩/精确线性代数），
  不得只凭观察；
- 记录 `m_max`（构造上限）与实际上界比较；若 `m` 不足（上界更小），如实写负结果；
- 线性相关函数必须剔除并记录（否则 `m` 虚高 = 错误）。

### 12.3 半径之积的计算口径

- p 进半径：`R_p(g) := 1 / limsup_n |[t^n] g|_p^{1/n}`（或等价的显式公式/超几何估值）；
  对每个 `p ∈ S` 给出**公式或可复现算法**，并注明是精确还是估计；
- 无穷位半径：`R_∞^φ(g)` 定义；`φ` 取 Belyi/β 时用 `|φ′(0)|`（共形半径）并给出出处；
- 半径积：`𝓡_S(f,x,φ) := R_∞^φ(f∘x) · ∏_{p∈S} R_p(f∘x)`；`S` 的精确定义（坏素数、分母素数、
  `p|m` 的位是否并入）；
- 口径约束：同一整体坐标；`x*f∈Z[[t]]`/`φ*f∈O(D)` 给出的 `R≥1` 只是必要条件；
  overconvergence 因子必须计入（不得只在有利的一侧乘）；
- 数值精度：给出文件/脚本/版本；符号与数值结果分别列。

### 12.4 `cost(m)` 的定义

- A3 的目标不等式形状：`log c ≤ C·log rad + cost(m)`（或等价形式），**先写清 `cost(m)` 的显式定义**：
  哪些损失计入（分母类型 `R=Z[1/N]` 的损失、`p|m` 的位、覆盖分歧/次数、`m` 本身的维数项）；
- 必须给出 `cost(m)` 与 k 的依赖关系（是否随 k 线性增长）；
- 判定用：`cost(m)` 不随 k 线性增长 ⇒ 有戏；`cost(m)` 吃掉全部增益 ⇒ STOP；
- 禁止：把未计入的损失藏进常数、或事后调参使 `cost` 变小。

### 12.5 试金石回答（四问）

1. 主张量词范围（家族 `(1,3^k−1,3^k)` 的 k 范围 + 20 个已知高质量三元组 + 条件）；
2. “`3^k−1` 不是近似完全幂”的信息从哪一步进入（例如：`u=a/c` 的分母素数进入 S、
   p 进半径乘积、F4 覆盖参数、或明确“本实验不使用、仅作后续输入”）；
3. 丢失检验：去掉该信息后主张退化为哪个更弱陈述；
4. 若 Q2/Q3 答不出 ⇒ 该主张 STOP-NO-TOUCHSTONE。

### 12.6 停止判据（预登记，不得事后放宽）

- **PASS（有戏）**：至少一族得到 `log c ≤ C·log rad + cost(m)`，且 `cost(m)` 不随 k 线性增长、
  `𝓡_S > 1` 在所有样本上成立（样本内无反例）；
- **STOP**：`cost(m)` 总是吃掉全部增益（如 `cost(m) ≥ (1−o(1))·k log 3`）、或 `𝓡_S ≤ 1`、
  或 `m` 总 ≤ Theorem 2.0.1 上界；
- **PARTIAL**：只有 F4 常数不等式（`1 ≤ e·I_1/log4`）而无 abc 增益 ⇒ 明确写“无信号”，不得包装；
- 样本/参数区间/阈值必须**在实验前**写入文档；实验后只允许追加新样本，不得改判据。

### 12.7 附录：A3 数据表必备列（每行一条三元组）

`三元组 (a,b,c) | k/标签 | S（坏素数） | u=a/c | 每 p∈S 的 R_p | φ 的 |φ′(0)| | 𝓡_S |
Theorem 上界 e·∫log⁺|p∘φ|/log|φ′(0)| | m（线性无关数） | cost(m) | 判定（PASS/STOP/PARTIAL）`

并要求：每行标 `NUMERIC`/`MODEL`；命令/脚本/数据文件路径；不能只给截图或口头数。
