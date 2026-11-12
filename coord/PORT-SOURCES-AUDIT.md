# PORT-SOURCES-AUDIT — FLT271 与 anthropic Definitions（A848，stage4）

日期：2026-11-12。无 Lean 文件改动。结论先行：

| 源 | 许可/归属 | 占位/axiom/sorry | 与 v4.32.2 差异 | 可 port? |
|---|---|---|---|---|
| ① FLT271（ImperialCollegeLondon/FLT @ a3210204） | Apache-2.0；**每个 .lean 保留原始版权头**（Kevin Buzzard 等）；无需 NOTICE/ATTRIBUTION | 未本地核（需 clone 后扫）；上游为完成的形式化，但必须实测 | toolchain **v4.35.0**（3 个 minor 之上）；mathlib **56a0058**（2026-10-13）vs 我们 905b958（2026-07-28） | **可安全 port，但需机械降级**（见 §1） |
| ② anthropic Definitions（本地 clone @6e837e75，v4.33.1） | Apache-2.0 + NOTICE + ATTRIBUTION.md；**文件本身无归属头**（byte-for-byte 发布，仅 5 文件例外）；ATTRIBUTION 按文件列出 106 个上游派生文件 | **实测 0 opaque / 0 axiom / 0 sorry**（1450 文件全扫）；实心定义，非占位 | toolchain **v4.33.1**（1 minor）；mathlib **db584cd6** | **可安全 port**（我们已 port 的 19 个 Def_* 均不在 ATTRIBUTION 派生列表 ⇒ 仅需仓库级 Apache-2.0 归属） |

## 1. FLT271：license / attribution / toolchain / mathlib rev

### 1.1 元数据（GitHub API 核对）

| 项 | 值 |
|---|---|
| repo | ImperialCollegeLondon/FLT |
| rev | a3210204ad88（commit date 2026-10-22T16:15:55Z，message: "chore: bump mathlib to 56a0058 (v4.35.0), fix breaking changes (#1205)"） |
| LICENSE | Apache License 2.0（11,357 B，与 Apache-2.0 标准文本一致） |
| 归属方式 | 每个 .lean 文件首部保留原始版权头，例：`Copyright (c) 2025 Kevin Buzzard. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE. Authors: ...` |
| NOTICE / ATTRIBUTION.md | **不存在**（404）——FLT 仓库以文件内头 + LICENSE 覆盖归属，不依赖额外 NOTICE 文件 |
| lean-toolchain | leanprover/lean4:**v4.35.0** |
| mathlib rev | **56a005855ea17e0b0958f73ec801ae140b0a1679**（2026-10-13，"bump toolchain to v4.35.0"） |
| 我们 | leanprover/lean4:**v4.32.2**，mathlib **905b95818e**（2026-07-28，"bump toolchain to v4.32.2"） |

### 1.2 与 v4.32.2 的差异（port 风险）

- **Lean 版本**：v4.35.0 → v4.32.2（跨 3 个 minor）。已知不兼容点：v4.35 的 `module` 语法与 `public import`；
  我们 `tools/port_fix_rules.txt` 已有 A787 机械规则（`(?m)^module$`→空行、`(?m)^public import `→`import `），
  可直接复用；其余 API 差异需按编译错误逐条机械修复。
- **Mathlib**：56a0058（v4.35.0 时代，2026-10-13）vs 我们 905b958（v4.32.2 时代，2026-07-28）——
  约 2.5 个月 mathlib 演进；上游 FLT 已在新 mathlib 上编译，降级会触发 API 重命名/签名漂移
  （我们此前 port 旧 FLT 时已见 `Ideal.isMaximal_*` 等改名；新树需要重新收集规则）。
- 结论：**许可/归属无阻塞**；工作量为机械降级 + 全量编译验证。须先 clone a3210204 到本地再统计
  文件数、sorry/axiom、以及实际编译通过率（本轮无本地副本，未做编译）。


## 2. anthropic Definitions（v4.33.1）：license 与占位检查

### 2.1 元数据（本地 clone `tmp/external/flt-lean`）

| 项 | 值 |
|---|---|
| repo | anthropics/fermats-last-theorem（README: "Fermat Last Theorem in Lean 4"，Anthropic, PBC） |
| 本地 HEAD | 6e837e75355538c7f80bab5b956861e86c4eacc2（2026-09-24，merge PR #9） |
| LICENSE | Apache License 2.0（11,357 B） |
| NOTICE | 有："Fermat Last Theorem in Lean 4 / Copyright 2026 Anthropic, PBC / Apache License 2.0"；
  并列出第三方受 Apache-2.0 许可的来源（Imperial FLT、flt-regular、Mathlib 等） |
| ATTRIBUTION.md | 有（49,922 B）：**file-by-file** 列出 106 个含 Imperial FLT/flt-regular 材料的文件
  （Definitions/ 54 个、P2M/Sol/ 52 个）及 23 个重现 Mathlib 文本的文件；说明 "Lean files are published
  byte-for-byte ... carry no attribution headers, apart from five files ..." |
| lean-toolchain | leanprover/lean4:**v4.33.1** |
| mathlib | **db584cd6d46c92f209a44c0f1c829460d327499d** |

### 2.2 占位检查（实测）

- `Definitions/` 共 **1450** 个 `.lean` 文件，全部扫描：**opaque 0、axiom 0、sorry 0**（`^\s*opaque`、`^\s*axiom`、`\bsorry\b` 匹配）；
- 抽查内容为实定义/定理（例：`Def_AlgebraicCurve_DivisorClassGroup.lean` 含 `structure Place`、
  `theorem _root_.ValuationSubring.not_isField_of_ne_top`、`def deg` 等 17 KB 实质内容；
  `Def_AlgebraicCurve_AdelicIndex.lean` 18.6 KB，含 `LSpace`、`ell`、`ConstantsAreBase` 等），
- 结论：**不是占位/carrier 空壳**；anthropic Definitions 是实心定义 + 定理集合。

### 2.3 我们已经 port 的 19 个 Def_* 的归属核对

- 19 个已 port 文件（`tmp/external/ported/flt/Definitions/Def_*.lean`，全部 19/19 有 olean）：
  AdelicIndex、CanonicalDivisor、CechSectionsOfDivisor、DivisorClassGroup、IsCurveOver、LocalResidue、
  RegularDifferentials、Repartitions、RiemannRochRows、SerrePairing、WeilOfKaehler（11 个 AlgebraicCurve），
  CoherentBaseChange、NeronModelPropertyBundleCarrier、SmoothProperCurveBase、SmoothProperCurveFiniteMapData、
  TwoAffineOpenCover、TwoChartCech（6 个 AlgebraicGeometry），CanonicalDivisor、CanonicalDivisorUniformizer（2 个 ModularCurve）；
- **逐一在 ATTRIBUTION.md 中检索：0/19 出现** ⇒ 这 19 个是 anthropic **原创**（非 Imperial FLT/flt-regular 派生），
  因此只需仓库级 Apache-2.0 归属（我们已加的 port 横幅 + LICENSE 引用即可），**无需复制 ATTRIBUTION 条目**；
- 若未来 port `Definitions/` 的其它文件（尤其 ATTRIBUTION §1–§3 列出的 54 个 Definitions 文件），
  **必须逐文件复制 ATTRIBUTION.md 中对应的上游版权头/作者列表**（因上游文件已被去头发布），并附带 NOTICE。

### 2.4 与 v4.32.2 的差异

- Lean v4.33.1 → v4.32.2（1 个 minor）：比 FLT271 小；我们已成功 port 这 19 个 Definitions，
  说明该 drivetrain 可行（`port_fix_rules.txt` 的既有规则覆盖了已见差异）；
- mathlib db584cd6（v4.33.1 时代）vs 我们 905b958（v4.32.2）：已有 19/19 编译成功的实证。

## 3. 判定汇总

| 源 | 可安全 port? | 理由 / 备注 |
|---|---|---|
| FLT271 @ a3210204（v4.35.0，mathlib 56a0058；本地 `tmp/external/flt271`） | **可（需机械降级）** | Apache-2.0 + 文件内版权头 ⇒ 许可/归属合规；无 NOTICE 需求；主要工作量 = v4.35→v4.32 机械降级 + mathlib 2.5 个月 API 漂移 + 全量编译。**实测：271 lean / 70 sorry / 3 axiom 声明**（`Assumptions/{KnownIn1980s,Mazur,Odlyzko}`）、0 compiled；Patching 14 = 7 顶层 + 7 Utils，import 闭包 19；首失败 = `Mathlib.Topology.Algebra.Group.Neighborhood` **模块源码缺失**（非 olean 缺失） |
| anthropic Definitions（v4.33.1） | **可（已 port 19/19）** | Apache-2.0；**无 opaque/axiom/sorry**（1450 文件实测）⇒ 非占位；已 port 的 19 个为 anthropic 原创（不在 ATTRIBUTION 派生列表）⇒ 仅需仓库级归属；若 port 其它 Definitions 派生文件，须逐文件复制 ATTRIBUTION 条目 |

## 4. 未核对 / 下一步

1. **FLT271 本地 clone 已完成**（A868 复核）：271 lean / 70 sorry / 3 axiom 声明 / 0 compiled；下一步是 v4.35→v4.32 降级编译 + 补 `Mathlib.Topology.Algebra.Group.Neighborhood` 模块；
2. FLT271 的 mathlib 差异量（提交数/API 改名清单）未逐条列举（GitHub compare API 响应过大被截断）；
3. anthropic repo 的 `P2M/`、`Theorems/` 已在 A852 补审（见 §5–§6）；FLT271 现已有本地 clone（A868），计数/首错已复核；
4. 建议把本文件与 `coord/FLT-PORT-EVIDENCE-AUDIT.md`、`coord/flt-port-sha256.txt` 一起作为 port 合规/证据隔离依据。


---

## 5. A852 追加：anthropic `P2M/` 与 `Theorems/` 审计

### 5.1 规模与结构（本地 clone `tmp/external/flt-lean`）

| 目录 | .lean 文件 | 总字节 | 结构 |
|---|---|---|---|
| `P2M/` | **29,507** | ~840.5 MB | `P2M/Sol/` 29,505 个解文件 + `P2M/Derive/`（1）+ `P2M/Util.lean` |
| `Theorems/` | **29,504** | ~268.3 MB | 全部平铺：`Thm_<Mathlib 声明名>.lean` |
| `Definitions/` | 1,450 | ~12.2 MB | 见 §2（已审） |

- `P2M/Sol/S_<Name>.lean` 是**真实证明**（每文件证明一个 Mathlib 级定理/引理，如
  `S_AbsoluteValue_Completion_isUltrametricDist_of_isNonarchimedean`）；
- `Theorems/Thm_<Name>.lean` 是**声明包装**：`import Mathlib; import P2M.Util; import P2M.Sol.S_<Name>`，
  然后 `theorem <Name> ... := by p2m_exact_reverting @_root_.P2MW.S_<Name>.solution`；
  即“把 P2M 解包成 Mathlib 命名空间下的定理”，**不含独立证明**。

### 5.2 sorry / axiom / 占位检查（实测）

| 目录 | sorry | axiom（`^axiom`） | opaque | 备注 |
|---|---|---|---|---|
| P2M/（29,507 文件） | **0** | **0** | **0** | 含 `P2M/Util.lean`（tactic 定义）也 0 |
| Theorems/（29,504 文件） | **0** | **0** | **0** | 包装文件，无独立证明体 |

- 与 FLT ported tree（18 sorry / 15 knownin1980s）不同：P2M/Theorems **本目录扫描未见 sorry/axiom**；
- 但 `Theorems/` 依赖 `p2m_exact_reverting`（`P2M/Util.lean` 的 tactic）；审计仅确认源文本无 sorry/axiom，
  未验证 tactic 是否引入不可接受的封闭方式（仍需 port 后 gate `#print axioms` 抽检）；
- 文件大小：P2M/Sol 中位 15,291 B、最大 1,649,185 B；Theorems 中位 2,531 B、最大 218,201 B。

### 5.3 ATTRIBUTION 义务

- `ATTRIBUTION.md` 中 `P2M/` 文件被点名 **72** 个（§1–§3 的 Imperial FLT/flt-regular 派生清单，按文件名匹配）；
  这些文件 port 时必须逐文件复制上游版权头/作者（源文件 byte-for-byte 无头）。
- `Theorems/` 文件在 ATTRIBUTION.md 中 **0** 个被点名；但它们逐字重述 **Mathlib** 声明（`Thm_<Mathlib Name>`），
  ATTRIBUTION §4 只列 23 个“reproduce Mathlib text”文件 ⇒ **存在归属歧义**：
  若把 Theorems 当 Mathlib 声明复制，应保留 Mathlib 的 Apache-2.0 归属（Mathlib 作者/来源）；
  若只用 P2M/Sol（真实证明），则只需处理 72 个派生文件的归属。
- 结论：port P2M 闭包时，**必须附带 NOTICE + ATTRIBUTION.md，并对 72 个被点名文件逐一手动加头**。

## 6. 对 C 路线（Frey/modularity/height）有用的模块清单

说明：按文件名关键词统计（Theorems 与 P2M/Sol 同名一一对应；下表给 Theorems 侧的入口，实际 port 需其 P2M/Sol 证明闭包）。
数量为文件名匹配计数，**不代表已审内容**；具体目标需先提 import 闭包再评估规模。

| 主题 | 匹配文件数 | 代表模块（Theorems 侧） | C 路线用途 |
|---|---|---|---|
| **Frey 曲线/包** | 64 | `Thm_FreyPackage_frey_isModular`, `Thm_FreyPackage_atPNewLowering`, `Thm_FreyCurve_isPeuRamifieeAt_odd_of_integralForm`, `Thm_FreyCurve_freyCurveInt_apOfModel_three` | C0/C1/C2 核心：Frey 曲线构造、半稳定、level lowering 输入 |
| **模性/级降低** | 7,932（Modular 总） | `Thm_EisensteinWeightOne_e1Chi3IsModular`, `Thm_FreyPackage_frey_isModular`, `Thm_CuspForm_heckeLocal_*isResiduallyModular*` | C1（模性）、C2（level lowering） |
| **Taylor–Wiles / patching** | 23（Wiles）+ 8（TaylorWiles） | `Thm_TaylorWiles_exists_isTaylorWilesPrime`, `Thm_CuspForm_heckeLocal_exists_taylorWilesModule_*`, `Thm_ResidualGaloisRep_*isTaylorWilesPrime*` | C1 模性提升机制 |
| **Newform / CuspForm / Hecke** | 101 + 436 + 179 | `Thm_CuspForm_exists_isNewform_descent`, `Thm_CuspForm_atkinLehnerLin_*isNewform*`, `Thm_KatzModularForm_*` | C0/C3：newform、Hecke 特征、q-展开 |
| **Cerednik–Drinfeld / Shimura 曲线** | 28（Shimura）+ 750（EllipticCurve_，多为 QM/fake EC） | `Thm_CerednikDrinfeld_ShimuraCurveModel_*`（goodReduction/eichlerShimura 等） | C2/C3：Shimura 曲线、模参数化（§12.3(c)） |
| **Ribet 不可约性/降层** | 13 | `Thm_RibetIrr_irreducible_of_point_of_not_dvd`, `Thm_RibetIrr_isFlatAt_of_linearEquiv_baseChange` | C2 |
| **Galois 表示** | 422 | `Thm_CuspForm_HeckeGaloisRepDatum_detIsCyclotomic`, `Thm_AlgebraicCurve_rationalGaloisRep_*` | C1/C2：ρ̄ 构造与性质 |
| **Heights / Faltings 对象** | 199 | 名称含 Height 的 Mathlib-级引理（需闭包抽取确认具体目标） | C3（高度比较） |
| **Automorphic forms（adelic）** | 2,338 | `Thm_AutomorphicForm_*`（adelic GL、Hecke eigensystem） | C1/C3 背景；但体积巨大，优先级低 |

### 6.1 建议的 port 优先级（C 路线）

1. **最小可用目标**：`Thm_FreyPackage_frey_isModular`（及其 `P2M/Sol/S_FreyPackage_frey_isModular` 闭包）——
   直接对应 C1；先抽 import 闭包看规模（可能数百文件 + 依赖 Mathlib 部分）。
2. **C2 目标**：`Thm_FreyPackage_atPNewLowering`、`Thm_RibetIrr_*`（13 个）与 Taylor–Wiles 8 个入口；
3. **C0/C3 目标**：`Thm_CuspForm_*isNewform*`（101）与 Heights 类（需先按闭包筛选真正相关者）；
4. **暂缓**：AutomorphicForm（2,338）与 ModularCurve（7,708）——体量与 C 路线直接需要不成比例；
5. 每个目标 port 前必须：抽 import 闭包 → 核对 72 个 ATTRIBUTION 文件是否在内 → 机械降级 v4.33.1→v4.32.2 → 编译 → gate `#print axioms` 抽检（防 `p2m_exact_reverting` 隐藏 axiom）。

### 6.2 风险与限制

- 本审计只做了**文件名级筛选 + 源文本 sorry/axiom 扫描**，未编译、未验证这些定理的证明实体；
- `Thm_*` 只是 `P2M/Sol` 的包装，真实工作量在 `P2M/Sol` 闭包（文件数未知，需闭包抽取）；
- 归属：P2M 72 个文件需逐一手动加头；Theorems 重述 Mathlib 声明的归属方式未在 ATTRIBUTION 中明确，
  建议 port 时保留 NOTICE/ATTRIBUTION 并注明 Mathlib 来源；
- toolchain v4.33.1 → v4.32.2 的 API 漂移仍需逐文件修（Definitions 19/19 的经验可复用）。


---

## 7. A854：`Thm_FreyPackage_frey_isModular` 闭包与 port 方案

### 7.1 闭包规模（静态 import 闭包，Python 抽取）

| 项 | 值 |
|---|---|
| 目标文件 | `Theorems/Thm_FreyPackage_frey_isModular.lean`（本地 `tmp/external/flt-lean`） |
| 目标声明 | `theorem FreyPackage.frey_isModular (P : FreyPackage) : P.freyCurve.IsModular := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_frey_isModular.solution` |
| 闭包总文件数 | **55,981** |
| 按子树 | Definitions 1,403 / P2M 27,290 / Theorems 27,288 |
| **ATTRIBUTION 派生文件在闭包内** | **112**（Definitions 54 + P2M/Sol 58） |
| 未解析 import | **5**（本地 release 缺对应 Theorems 文件；见 §7.4） |
| 风险 token 扫描（闭包内） | sorry=0 / admit=0 / native_decide=0 / ofReduceBool=0 / implemented_by=0 / extern=0 / unsafe=0 / axiom=0 |

- 112 个 ATTRIBUTION 派生文件的完整清单：`coord/flt-frey-closure-attribution.txt`（port 时逐文件复制上游版权头/作者）。
- 注意：全量闭包 56k 文件，绝大部分是 Mathlib 级引理/包装；实际 port 需先做**可达性裁剪**
  （只保留目标证明真正需要的声明/模块），否则体积不可行。

### 7.2 port 归属操作（112 文件）

1. 从 `ATTRIBUTION.md` 提取每个文件的 upstream 行（upstream path + copyright holder + authors）；
2. 在移植后的文件头插入等价的 Apache-2.0 归属块（因上游文件被去头发布，必须由这张表恢复）；
3. 同步附带 `NOTICE` + `ATTRIBUTION.md` 原文到 port 目录，并在 port README 里引用；
4. 对 112 个文件逐一核对（含 Definitions 54、P2M/Sol 58）——完整清单见上述 txt。

### 7.3 `#print axioms` 抽检方案（port 后）

**允许集合（项目 gate）**：仅 `[propext, Classical.choice, Quot.sound]`（无 sorryAx、无 ofReduceBool/trustCompiler、
无 upstream axiom、无 implemented_by/extern/unsafe 产生的额外公理）。

**抽检步骤**：

1. **静态前置**：closure 风险 token 扫描（已做：全 0）——`sorry`/`admit`/`native_decide`/`ofReduceBool`/
   `implemented_by`/`extern`/`unsafe`/`axiom`；
2. **tactic 封闭性**：`p2m_exact_reverting` 定义在 `P2M/Util.lean`，实现为 Lean metaprogram：
   `revert` 全部局部假设 → `elabTermEnsuringType` 对目标类型检查指定 term → 检查无 metavariable → `assign`；
   语义等价于 `exact`，**不引入新公理**（无 `native_decide`/`ofReduceBool`/`sorry` 调用）。port 后仍需实测确认；
3. **目标层打印**：probe 文件（port 后，用我们自己的 `lake env lean`）：
   ```lean
   import <ported target module>
   #print axioms FreyPackage.frey_isModular
   #print axioms P2MW.S_FreyPackage_frey_isModular.solution
   ```
   期望两行均为 `[propext, Classical.choice, Quot.sound]`；若出现 `sorryAx`/`Lean.ofReduceBool`/`knownin1980s`
   /自定义 axiom ⇒ 该目标 FAIL，标注不可依赖；
4. **源解层打印**：对 `P2MW.S_FreyPackage_frey_isModular.solution` 也打印（真实证明体在 P2M/Sol），
   防止包装层干净而源层有隐藏公理；
5. **批量抽检**：对闭包内 **抽样 10–20 个** P2M/Sol 文件（按大小/pagerank 选），逐一 `#print axioms` 其主声明，
   确认无额外公理；若抽样出现异常，扩大到全闭包；
6. **机械判据脚本**（建议）：收集 `#print axioms` 输出 → grep `{sorryAx, ofReduceBool, trustCompiler, knownin1980s, implemented_by}`，
   任一命中 ⇒ FAIL；否则 PASS。

### 7.4 已知阻塞项

- 闭包有 **5 个未解析 import**（本地 anthropic release 缺对应 `Theorems/Thm_*.lean` 文件）：
  1. `Theorems.Thm_AlgebraicCurve_rationalGaloisRep_tmul_eq_tmul_perm_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_...`
  2. `Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_gl3Translates_...`
  3. `Theorems.Thm_LanglandsTunnell_exists_agreesAwayFromFinite_twist_archCasimir_...`
  4. `Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_supersingularAffineChart_...`
  5. `Theorems.Thm_ModularCurve_XOneP_exists_coprime_algEquiv_finset_addMonoidHom_...`
  （本地存在近似名文件，如 `..._of_tame_of_dvd` 版本；说明 release 里 import 名与文件名有 5 处不一致）
  ⇒ port 前需先修这 5 条 import（重命名或补文件），否则目标无法编译；
- 全量闭包 56k 文件不可直接 port：需做可达性裁剪（建议用 Lean 的 import 分析或按目标声明依赖裁剪）；
- 本审计为静态 import 闭包，未编译，未验证裁剪后的可编译性。
