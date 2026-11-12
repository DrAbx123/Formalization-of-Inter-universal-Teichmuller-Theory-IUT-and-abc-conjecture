# FLT PORT EVIDENCE AUDIT — 排除记录 + §12 外部定理来源审计

日期：2026-11-12（A845，stage4）。无 Lean 文件改动。

## 0. 结论

1. tmp/external/ported/flt 不可用作为 green 证据：18 处 sorry、15 处 knownin1980s
   （FLT repo 的 axiom knownin1980s {P : Prop} : P）、仅 34/150 编译出 olean，
   且缺模形式/newform、Shimura 曲线、模参数化次数 δ、Petersson 范数、Faltings 高度、
   Ribet/Taylor-Wiles 机制、ABC 三元组构造器。从 green 证据集排除；当前 0 个 Lean 文件
   导入该树（隔离，不影响既有 gate）。
2. §12 计划的外部定理清单已逐条核对来源：均为已发表定理（Wiles/Taylor-Wiles/BCDT、Ribet、
   Mazur、Mestre-Oesterlé），但仓库内全部未机器化（MestreOesterleBound 出现 0 次），
   且 ROUTES 自列多处“凭记忆”项；这些只能作为显式 Prop 参数（class-B 外部输入），不得当 green。
3. 项目路线状态：A/B 已停止，仅 C 路线（Frey/modularity/height）继续（见 coord/ROUTE-C.md、
   ROUTE-C-INVENTORY.md 与 lead A844/A845 指令）。

## 1. FLT ported tree 不可用证据（排除记录）

### 1.1 树清单与出处

| 子树 | 文件数 | 来源 | rev | 原始版权 |
|---|---|---|---|---|
| Definitions/ | 19 | github.com/anthropics/fermats-last-theorem | commit 6e837e75 | LANA Project（Apache-2.0） |
| FLT/ | 131 | github.com/ImperialCollegeLondon/FLT | commit f6c6a2f | Kevin Buzzard 等（Apache 2.0） |
| 合计 | 150 | 两个上游混合 | — | — |

- 所有 150 个文件都含 porting 横幅（Ported for reuse from <repo> (commit ...), License: see source
  repo LICENSE (Apache-2.0); attribution retained. Imports rewritten ... v4.32.2）；
- 131 个 FLT 文件另有原始 Copyright (c) 2025 ... Released under Apache 2.0 头。
- MANIFEST.json 不完整：只记录 anthropics/fermats-last-theorem@6e837e75 与 1 个文件；
  未记录 ImperialCollegeLondon/FLT@f6c6a2f（131 文件）、无任何哈希字段。

### 1.2 不可用硬指标（实测）

| 指标 | 值 | 说明 |
|---|---|---|
| sorry 出现 | 18 | 分布在 KnownIn1980s、GaloisRep、EllipticCurve/Torsion、Automorphic、HardlyRamified/Frey 等 |
| knownin1980s 出现 | 15（ROUTE-C 记 16） | 上游 axiom knownin1980s {P : Prop} : P，属 axiom 机制 |
| 编译 olean | 34 / 150 | 仅 Definitions 19/19 与 FLT 约 15 个 |
| 模形式 / newform | 缺 | 无 ModularForm/Newform/Weight/Cusp 文件；AutomorphicForm 仅抽象骨架且未编译 |
| Shimura 曲线 | 缺 | 无 Shimura 文件 |
| 模参数化次数 δ | 缺 | 无 parametrization degree |
| Petersson 范数 / Faltings 高度 | 缺 | 无 |
| Ribet / Taylor-Wiles 机制 | 缺 | 无降层/模性证明 |
| ABC 三元组构造器 | 缺 | FreyPackage 面向 a^p+b^p=c^p，非 ABC |

结论：不得作为任何 Lean 证据。若未来复用，须全树重新 port、去掉 sorry/axiom、经 gate trio 验收；
当前仅可作参考骨架/上游定义清单。

### 1.3 哈希完整性

- 仓库未记录上游/移植后哈希（MANIFEST 无哈希字段）；无法与上游逐一比对。
- 本次已生成机器可读哈希清单：coord/flt-port-sha256.txt（150 行，按路径排序）；汇总：
  - aggregate(all 150) = cba5fe4595ff6fd062dbea127dcd24dc5d319b288ea65391b11adf0f5aa71eb8
  - aggregate(anthropics@6e837e75, 19) = d30194436e987b9f0bb93456243cae4dfdda0462c297e49b860e98d89c8f3228
  - aggregate(ImperialCollegeLondon/FLT@f6c6a2f, 131) = 23feec89ebe457431d1a422474ae0b26f93db389aaf404c4c42bf0d9e2f84882
- 建议：把 coord/flt-port-sha256.txt 作为完整性基线；后续任何修改须重算并在审计中更新。

### 1.4 tools/port_fix_rules.txt 修改历史

| 文件 | 字节 | mtime (UTC) | 行数 |
|---|---|---|---|
| tools/port_fix_rules.txt.bak-a787 | 1260 | 2026-11-09T22:04:54Z | 21 |
| tools/port_fix_rules.txt（当前） | 1955 | 2026-11-11T16:45:11Z | 43 |

- 当前版本 = bak-a787 + 21 行新增（A787 块）：
  module/public import 改 import（v4.35 module 语法）、Ideal.isMaximal_* 重命名、
  under_def 桥、public/expose section 语法等机械规则；
- 无其他 .bak 系列（仓库中 .bak* 共 69 个，与 flt port 相关的仅 tools/port_fix_rules.txt.bak-a787）；
- 规则文件只用于 port 工具链，本次审计不改动。

## 2. §12 计划外部定理清单与来源审计

来源：coord/ROUTES-FINAL-GAP.md §12.2（外部定理清单）+ §12.3。逐条给出处并标注状态。

| # | 定理（§12 用途） | 来源 | 核对状态 | Lean 状态 |
|---|---|---|---|---|
| E1 | 半稳定椭圆曲线模性（§12.2） | A. Wiles, Modular elliptic curves and Fermat Last Theorem, Ann. of Math. 141 (1995) 443-551, DOI 10.2307/2118559 | 题名/期刊/年确认（web 检索） | 未机器化 |
| E2 | Hecke 代数环论性质（配合 E1） | R. Taylor, A. Wiles, Ann. of Math. 141 (1995) 553-572, DOI 10.2307/2118560 | 题名/期刊/年确认 | 未机器化 |
| E3 | Q 上所有椭圆曲线模性（wild 3-adic） | C. Breuil, B. Conrad, F. Diamond, R. Taylor, J. Amer. Math. Soc. 14 (2001) 843-939, DOI 10.1090/S0894-0347-01-00370-8 | 题名/期刊/DOI 确认（AMS 页面） | 未机器化 |
| E4 | Ribet 降层（§12.2/§12.3） | K. Ribet, On modular representations of Gal(Qbar/Q) arising from modular forms, Invent. Math. 100 (1990) 431-476, DOI 10.1007/BF01231195 | 题名/期刊/DOI 确认（Springer 引文页） | 未机器化 |
| E5 | Mazur 挠点（§12.2 Θ-data 合法性） | B. Mazur, Modular curves and the Eisenstein ideal, Publ. Math. IHES 47 (1977) 33-186, DOI 10.1007/BF02684339 | 题名/期刊/DOI 确认（Numdam） | 未机器化 |
| E6 | Mazur 素度同源（§12.2） | B. Mazur, Rational isogenies of prime degree, Invent. Math. 44 (1978) 129-162, DOI 10.1007/BF01390348 | 题名/期刊/DOI 确认（NII/Springer） | 未机器化 |
| E7 | Mestre-Oesterlé 1989（§12.2 核心：素导子时 e_p <= 5，例外 p=11,17,19,37） | J.-F. Mestre, J. Oesterlé, Courbes de Weil semi-stables de discriminant une puissance m-ième, J. reine angew. Math. 400 (1989) 173-184, DOI 10.1515/crll.1989.400.173 | 题名/Crelle 卷 400/zBmath 记录确认；精确陈述（例外集合）ROUTES 自注凭记忆，未逐条核对 | 未机器化；计划写法 paperGap_of_primeConductor (hMO : MestreOesterleBound)，当前仓库 MestreOesterleBound 出现 0 次 |
| E8 | Ribet-Takahashi 比值 δ_{1,N}=δ_{N,1}∏e_p（§12.3(c)） | R. Takahashi（Ribet-Takahashi 关系）；ROUTES 自注凭记忆引用 | 待核对原始文献；未逐字确认 | 未机器化 |
| E9 | Pasten 2018 + 2026-09 预印本（Shimura 曲线参数化次数 << N^{2+ε}） | H. Pasten, Shimura curves and the abc conjecture 预印本（mat.uc.cl/~hector.pasten/preprints/ShABC.pdf）；2026-09 预印本 ROUTES 自注没有读过正文 | 2018 预印本 URL 确认；2026 预印本未核 | 未机器化 |
| E10 | Baker 方法型上界、Hall 猜想、van Frankenhuijsen 常数（§6.2/§12.3(b)） | ROUTES 自注凭记忆；Hall 为猜想，非定理 | 未核对 | 未机器化 |
| E11 | Faltings 高度、Petersson 范数、Néron 周期（§12.3(c)） | 经典结果；ROUTES 未给具体文献 | 未核对 | 树中缺（见 §1.2） |

关键审计结论：

1. §12.2 中作为 Lean 参数化的唯一显式外部定理是 E7（Mestre-Oesterlé，MestreOesterleBound : Prop）；
   其余 E1-E6 用于论证 Θ-data 合法性与路线背景，不是 SSIneq 证明的直接输入；
2. E7 的精确陈述（e_p <= 5 与例外 p=11,17,19,37）在 ROUTES 中自注凭记忆，本次 web 核对只确认了
   文献存在与卷期，未验证定理的精确常数/例外；在把它写成 Prop 前须逐字对照原文（Crelle 400, 173-184）；
3. E8-E11 是 §12.3 研究性内容，不得进入 Lean 证据链；
4. 所有外部定理在仓库中均 0 次机器化（class-B 外部输入），只能作为显式假设/参数，不得称 green。

## 3. 路线状态记录

- 项目路线状态（lead A844/A845 声明 + 文档）：A/B 已停止，仅 C 路线（Frey/modularity/height）继续；
- 文档证据：coord/ROUTE-C.md（ROUTE C — Frey / modularity / height route，Status 2026-11-12，
  源 = tmp/external/ported/flt）、coord/ROUTE-C-INVENTORY.md（树清单与 C 组件矩阵）；
- C 路线当前仅 inventory + gap statement（非证明）：C0-C4 全部 PENDING（见 ROUTE-C.md §1）；
- FLT port 树按 §1 排除出 green 证据集；C 路线若继续，必须自行 port/证明目标对象，不得引用该树中
  的 sorry/axiom 结果。

## 4. 复现/数据

- 计数命令：遍历 tmp/external/ported/flt/**/*.lean 读首部横幅与全文匹配 sorry/knownin1980s/Copyright；
- 哈希：coord/flt-port-sha256.txt（含 aggregate 与逐文件 SHA256）；
- 规则历史：diff tools/port_fix_rules.txt.bak-a787 tools/port_fix_rules.txt（21 行新增）；
- 外部文献核对：web 检索（zbmath/Crelle 400/AMS JAMS/Springer 引文页/NII/Numdam），见 §2 表内链接；
- 无 Lean 文件改动。
