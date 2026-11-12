# E7-SOURCE-AUDIT — Mestre–Oesterlé 1989 条目来源核验（A859，stage4）

日期：2026-11-12。**无 Lean 文件改动。**

## 0. 状态与阻塞

- 本轮任务要求审计 `coord/E7-LITERATURE.md` / `coord/EXTERNAL-THEOREMS.md`；**两文件在审计时均不存在**
  （`coord/` 下无匹配文件，qpilot 尚未产出）⇒ 无法做“逐条对照”审计；本文件为**独立来源核验**，
  待两文件出现后可直接比对。
- 本文件仅核验 E7（Mestre–Oesterlé 1989）的文献元数据与陈述可靠性。

## 1. E7 文献元数据（已核验）

引用（ROUTES-FINAL-GAP §12.2 所引）：

> J.-F. Mestre, J. Oesterlé, « Courbes de Weil semi-stables de discriminant une puissance m-ième »,
> J. reine angew. Math. **400** (1989), 173–184.

| 字段 | 核验值 | 来源 | 状态 |
|---|---|---|---|
| 标题 | « Courbes de Weil semi-stables de discriminant une puissance m-ième » | Crossref + zbMATH | ✅ VERIFIED |
| 作者 | Mestre, J.-F.; Oesterlé, J. | zbMATH OAI 记录 `oai:zbmath.org:4134201`（`dc:creator`） | ✅ VERIFIED |
| 期刊 | Journal für die reine und angewandte Mathematik (Crelles Journal) | Crossref `container-title`；zbMATH `dc:source` | ✅ VERIFIED |
| 卷/年 | Band 1989, Heft 400（卷 400，1989） | Crossref `volume=1989`；zbMATH `J. Reine Angew. Math. 400` | ✅ VERIFIED |
| 页码 | 173–184 | Crossref `page`；zbMATH `dc:source` | ✅ VERIFIED |
| DOI | **10.1515/crll.1989.400.173** | Crossref API 返回该 DOI 的完整元数据 | ✅ VERIFIED |
| 出版日期 | 1989-09-01 | Crossref `issued/published` | ✅ VERIFIED |
| 语言 | French | zbMATH `dc:language` | ✅ VERIFIED |
| 出版商 | Walter de Gruyter GmbH, Berlin | Crossref/zbMATH | ✅ VERIFIED |
| MSC | 14H25; 14H52; 11F11; 14G25; 14H45 | zbMATH `dc:subject` | ✅ VERIFIED |

核验请求（复现）：
- `https://api.crossref.org/works/10.1515/crll.1989.400.173`（200，元数据如上）
- `https://oai.zbmath.org/v1/?verb=GetRecord&metadataPrefix=oai_dc&identifier=oai%3Azbmath.org%3A4134201`
  （200，XML：title/source/creator/language/subject）

## 2. 被引用的**数学陈述**（未核验，标不可靠）

ROUTES §12.2 的用法（原文）：

> “外部定理给 e_p := ord_p(Δ_min) ≤ 5（p > 37 时 ≤ 2）”；
> “Mestre–Oesterlé 1989（素导子时 |Δ| = p 或 p²，例外 p = 11、17、19、37）”。

| 陈述要素 | 当前引用 | 核验状态 |
|---|---|---|
| 假设：E/Q 半稳定？ | 未明写（§12.2 只写“素导子时”） | ❌ **未核验** |
| 假设：导子为素数 p？ | “素导子时” | ❌ 未核验 |
| 结论：|Δ_min| = p 或 p²？ | 如引 | ❌ 未核验 |
| 例外：p ∈ {11,17,19,37} 的精确含义（曲线例外/指数例外） | 如引 | ❌ 未核验 |
| 推论：e_p ≤ 5（p>37 时 ≤2） | ROUTES 推导 | ❌ 未核验（依赖上一行） |
| 定理编号/页码定位（在 173–184 中的位置） | 未给出 | ❌ 未核验 |

**说明**：原文为法语、De Gruyter 付费墙；本轮只能核验到文献元数据，**无法读取正文**。
ROUTES 文件本身自注“Mestre–Oesterlé 定理的精确陈述（例外 p = 11、17、19、37）凭记忆”——
与本审计结论一致：**精确陈述不可靠，不得作为 Lean 显式 Prop 的依据**，直到逐字核对原文。

## 3. 可靠性判定汇总

| 类别 | 判定 |
|---|---|
| DOI / 期刊 / 卷期 / 页码 / 年份 / 作者 / 语言 | **可靠（已核）** |
| 定理的精确假设与结论（含例外集合、e_p 界） | **不可靠（未核，恰为 ROUTES 自注凭记忆处）** |
| 与 §12.2 的推论链（素数导子 ⇒ e_p ≤ 5） | **未核**；在把 `MestreOesterleBound` 写成 Lean 假设前必须逐字核对 |

## 4. 后续动作（建议）

1. 取得 Crelle 400 (1989) 173–184 正文（图书馆/De Gruyter），逐字摘录：定理编号、假设（半稳定/导数/‘Weil curve’定义）、
   结论公式、例外列表；把摘录附在本文件；
2. 若结论为 |Δ| = p 或 p²（例外 4 个素数），据此推 e_p ≤ 5（p>37 时 ≤2）的推导也需逐步写清（哪一步用到例外）；
3. 在此之前，`MestreOesterleBound` 只能作为 **NAMED 外部定理占位**，不得称 green、不得进入最终链；
4. 待 qpilot 的 `coord/E7-LITERATURE.md`/`EXTERNAL-THEOREMS.md` 出现后，把其条目与本文件逐字段比对，
   重点检查：DOI 是否写成 `10.1515/crll.1989.400.173`、卷是否写 `400`（非 1989 卷号歧义）、例外是否写成 4 个素数、
   是否把法语标题写对。

---

## 5. A863：`#print axioms` 抽检 + P2018/P2026 条目核验

### 5.1 四个新文件 trio 抽检（PASS）

probe：`import` 四个文件 + `#print axioms`（`tmp/a863_axiom_probe.lean`，`lake env lean` EXIT=0）。

| 文件 | 声明 | `#print axioms` 结果 | 判定 |
|---|---|---|---|
| Mzk1CRouteAssemblyActual | abcConjecture_of_cRouteAssembly | propext, Classical.choice, Quot.sound | ✅ trio |
| Mzk1CRouteAssemblyActual | abcConjecture_of_routeC | 同上 | ✅ |
| Mzk1CRouteAssemblyActual | freyPackage_shape_of_assembly | 同上 | ✅ |
| Mzk1E7ReductionActual | e7_equiv_chain | 同上 | ✅ |
| Mzk1E7ReductionActual | rt_delta_of_product | 同上 | ✅ |
| Mzk1DExactLowerActual | L5CapsuleAverage_eq_sL | 同上 | ✅ |
| Mzk1DExactLowerActual | l6Reduced_of_dExactLower | 同上 | ✅ |
| Mzk1DExactLowerActual | ssIneqExplicit_of_dExactLower | 同上 | ✅ |
| Mzk1FreyConductorFinalActual | c4_poly_not_dvd | 同上 | ✅ |
| Mzk1FreyConductorFinalActual | freyDeltaNat_eq | **propext**（⊂ trio） | ✅ |

**结论：10/10 抽检声明均只依赖 trio 子集（无 sorryAx、无外部 axiom）** ⇒ 四个文件通过 gate。

### 5.2 P2018 / P2026 条目核验（与 E7-LITERATURE.md 一致性）

| 字段 | EXTERNAL-THEOREMS.md | E7-LITERATURE.md | 一致性 | 核验状态 |
|---|---|---|---|---|
| P2018 arXiv ID | 1705.09251 | 1705.09251 | ✅ | **snippet 级已核**（web 检索标题 “Shimura curves and the abc conjecture”；arXiv 本机域名不可达，export/browse 均非公共 IP） |
| P2018 版本/日期 | v4 (2018) | v1 2017-05-25、v4 2018-07-05 | ✅（两者不冲突） | ⚠ **未核**（arXiv 页不可达） |
| P2018 发表状态 | 未提 | “JEMS best current knowledge，arXiv 权威” | 无冲突 | ⚠ **未核** |
| P2026 arXiv ID | 2609.17390 | 2609.17390 | ✅ | **snippet 级已核**（标题 “Improved bounds for Szpiro’s conjecture”） |
| P2026 版本/日期 | v1 (2026-09-15) | v1；submitted 2026-09-15 | ✅ | ⚠ **未核**（arXiv 页不可达） |
| P2026 主定理编号 | Thm 1.1 | Thm 1.1 | ✅ | 两文档一致（均未直接对照原文；**待原文**） |
| P2026 推论编号 | Cor 1.2 / 1.3 | Cor 1.2 / 1.3 | ✅ | 两文档一致（待原文） |
| P2026 假设 | N=DM admissible（gcd=1, D squarefree, D 偶数个素因子）、ℓ∤N、h = Faltings height (非 stable)、常数绝对有效 | 同 | ✅ | 两文档一致（待原文） |
| P2018 Thm 1.5 / Cor 6.2 | L10 注明“原文 Cor 6.2” | 同（Thm 1.5 = Cor 6.2） | ✅ | 两文档一致（待原文） |
| P2018 Thm 1.3/1.4 | L10 未展开 | §3 列 Manin constant / cokernel | 无冲突 | 待原文 |
| P2018 精确编号完整性 | 未提 | 自注“P2018 Faltings-height 主定理编号 PENDING” | 无冲突 | E7-LITERATURE 的 PENDING 说明应同步到 EXTERNAL-THEOREMS |

**结论**：P2018/P2026 两条在两文档间**未发现矛盾**（ID、版本、定理编号、假设、推论编号一致）；
但 arXiv 页面本环境不可达，**版本/日期/发表状态均只到“两文档互证 + 搜索片段”级别，未读原文**，
故原文级核验状态仍为 **UNVERIFIED**。

### 5.3 不可靠 / 需修正条目

1. **E7 的 Mestre–Oesterlé 引用错误（EXTERNAL-THEOREMS §2 L3）**：文档写 “Mestre, *Formules explicites et minoration de conducteurs*, 1986；Oesterlé（显式公式）”，
   但 ROUTES/E7 实际引用的是 **Mestre & Oesterlé, « Courbes de Weil semi-stables de discriminant une puissance m-ième », J. reine angew. Math. 400 (1989) 173–184, DOI 10.1515/crll.1989.400.173**（本文件 §1 已核）。
   且 L3 的“工作形式”（`log N_E ≤ (1+o(1))·log rad(abc)`）与 ROUTES §12.2 的用法（`e_p ≤ 5`、`|Δ|∈{p,p²}`、例外 11/17/19/37）不一致 ⇒ **L3 判为不可靠，须替换/重写**。
2. **FLT271 patching 管道描述误导（§3.1）**：文档称首失败为 “mathlib olean 缺失（不是 port 错误）”，建议 `lake build Mathlib.Topology.Algebra.Group.Neighborhood` 后重试。
   实测：该模块在我们的 mathlib 905b958 **源码不存在**（mathlib 树仅有 `Mathlib/Topology/Neighborhoods.lean`），而 `tmp/external/flt271/FLT/Mathlib/Topology/Algebra/Group/Basic.lean:8` 直接 `public import Mathlib.Topology.Algebra.Group.Neighborhood`。
   ⇒ 不是“缺 olean”，而是**缺模块源码**（该模块属 mathlib 56a0058 / v4.35 时代）；`lake build` 无法生成，需要**移植该 Mathlib 模块**或改写，工作量与新风险须计入。
3. **“FLT/Patching/（14 文件）”表述**：实测 `FLT/Patching/` 顶层 7 个 `.lean`；再加 `FLT/Patching/Utils/` 7 个 = 14（与闭包 19=14+1+4 一致）⇒ 应改为“14 文件（7 顶层 + 7 Utils）”，否则易误读。
4. **arXiv 版本/日期/发表状态**：P2018 v4 2018-07-05、JEMS 发表；P2026 v1 2026-09-15、同行评审状态——本环境 arXiv 不可达 ⇒ 标 **UNVERIFIED**（不得当作已核事实写进依赖）。
5. **A 类 “0 sorry/0 axiom”**：与源文本扫描一致（P2M/Theorems 全扫 0），但 A1 的闭包有 112 个 ATTRIBUTION 派生文件与 5 个未解析 import（见 A854）⇒ “可直接采用”应限定为“以 class-B Prop 引用其语句，不编译”，不影响本条。
6. **lana-agents/heights rev `f4379dbc…`**：本会话未 clone，**UNVERIFIED**。

### 5.4 FLT271 行复核（§0 表）

实测本地 `tmp/external/flt271`：**271 lean / 70 sorry / 3 axiom 声明**（`FLT/Assumptions/{KnownIn1980s,Mazur,Odlyzko}.lean`）；
toolchain 文件 = `leanprover/lean4:v4.35.0`；mathlib rev = `56a005855e…` ⇒ 与 EXTERNAL-THEOREMS 表一致 ✅。
