# CHAIN2-ATTACK — 链二主线作战文档（A896 重写版）

Date: 2026-11-12 (A896 rewrite; supersedes A881/A884/A887 wording). **所有 lana 路径相对根 `Iut/` 树（`D:/lean/Iut/...`）。**

Status: **链二与目标等价（`req <= U`），不是“存活”**。模型层的“存在族/G”折叠成 `req <= U`；真正缺的是字典 `qPilotRegion subset P ⇒ (s-1)A <= VolShell P`，不是 G 候选。当前目标对象是否仍取 lana `SSIneq` 未定：**OPEN DECISION**。

## 0. 状态更正（相对 A881/A884/A887）

| 项 | 旧口径 | A896 口径 |
|---|---|---|
| 链二状态 | 程序性存活 / Phase 2 | **等价于目标 `req <= U`**，非独立内容；不称存活 |
| G1/G2/G3 | “真实 G 候选”，G1 首选 | **都不是约束候选**：G1 仅相等 PF ⇒ 唯一同构；G2/G3 是良定义/标度律 |
| M2-M4 | 模型级完成 | **接口占位**；模型引理多处 trivial |
| §7 量词 | 逐 (v,j) | **对 v 求和 + 对 j 做 procession 平均后的单个不等式** |
| 上箱对象 | VolShell ≤ U | 只给 `req <= U`，**不是 lana SSIneq**；目标变更待用户 |
| p=11 数据 | 单一值 | **两处矛盾**（e=n=1,r=0 vs e=10,r=1,n=10），待裁定 |

## 1. 塌缩引理：链二等价于 `req <= U`

模型：`shellVolume D = baseShell - allowedLower*logp`（`logp>0`），`V(t)=base - t*logp`。单调性：
- `V(t)` 对 `t` 严格递减，值域为整个 `Real`（模型允许任意实数 order 区间）；
- 因此“存在允许族/G 使 `req <= V <= U`”等价于 `req <= U`，不需要任何新几何。

形式化目标（模型级，仍 trivial）：

```text
theorem chain2_collapse (hreqU : req <= U) :
  exists D, qPilotOrd D in allowedInterval D and req <= shellVolume D and shellVolume D <= U
theorem chain2_collapse_iff :
  (exists family/G, req <= shellVolume family and shellVolume family <= U) <-> req <= U
```

**关键**: 这个 iff 是单调性 + qPilotOrd/区间可调的重新包装；它不证明 IUT 不等式。真正的缺口是：

```text
theorem real_dictionary (h : qPilotRegion subset P) :
  (s - 1) * A <= VolShell P
```

其中 `s = l(l+1)/12`、`A = |log q|/(2l)`（或 ROUTES §6.1 的等价记号）。`real_dictionary` 目前 **不存在**；它才是链二的真实内容。

## 2. C2.1/C2.2/C2.3（A896 真实对象口径）

### 2.1 C2.1：局部包含（仅作中间对象，不是最终目标）

`P(v,j) = union over holomorphic structures h of Theta(h,j)(LogShell_v)`；局部候选 `qPilotRegion subset P` 只能逐 (v,j) 陈述。**注意**：ROUTES §6.3 已用显式三元组反驳逐 capsule/逐素数局部上箱：`l=11, (1, 13^4-1, 13^4)`, `ord_13(q)=8 > 6.4`；所以不能把逐 (v,j) 局部包含当作最终定量目标。

### 2.2 C2.2：平均后的上箱

真实目标是 **对 v 求和、对 j 做 procession 平均后的单个不等式**：

```text
lstar = (l-1)/2;  weights w_v with sum_v w_v = 1
VolShellAvg = (1/lstar) * sum_{j=1..lstar} sum_v w_v * logVol(hull(P(v,j)))
UpperAvg      = (1/lstar) * sum_{j=1..lstar} sum_v w_v * UpperIUTIV(v,j)
theorem C2_2_avg : G family -> VolShellAvg <= UpperAvg
```

`UpperIUTIV` 必须是 IUT IV 的实际上界/论文 hull 上界；不是抽象 U。**逐 (v,j) 的 `VolShell(v,j) <= U(v,j)` 已被 §6.3 反驳，不得使用。**

### 2.3 C2.3：平均上箱 + 字典 ⇒ 目标不等式

```text
theorem chain2_average_target
  (hP : averaged qPilot containment) (hG : G family) :
  (s - 1) * A <= VolShellAvg
```

这正是 `real_dictionary` 的平均版本。当前没有证明；模型层的 `chain2_model_ssIneq` 只是 `hmid.1`（见 §4 triviality）。

## 3. G1/G2/G3 不是约束候选（删除 G1 首选）

| ID | 实际内容 | 为什么不是 G 约束候选 |
|---|---|---|
| G1 `rlf_unique` | 相等 PF ⇒ 成员间唯一同构（`Iut/LogLink/Thm311Rest.lean:473`；`rlf_cocycle:479`；`mem_rposOrbit_iff:491`；`rlfData:523`；`Thm15v.unique:529`） | 只给“同一 PF 下唯一 iso”；`RposOrbit` 只是共用正数 c，**不限制族的选择/体积**；`Iut/Wall/Wall.lean:27` 说明 `1/s` 不作用于容器。 |
| G2 `componentVol_image_algEquiv` | 体积在结构同构/最小壳下不变（`Iut/Concrete/Ind1Invariance.lean:144,192`） | 只是 `VolShell` 良定义；不产生上界/约束。 |
| G3 `componentVol_prod_incl_smul_integral` | 精确标度律 `-(sum ord)*R`（`Iut/Concrete/LocalConstruct/ScaleVolume.lean:118`；`Prop14.lean:108`） | 只是体积公式；不规定 G，反而需要先有 G 才能算。 |

结论：**没有“G 候选”**。G 的真实定义/来源是未解决的数学输入；G1 的 `rlf_unique` 不能替代它。

## 4. M1-M6 与 triviality 标记

| 里程碑 | A896 状态 | 说明 |
|---|---|---|
| M1 接口 | 模型接口 green（`Mzk1Chain2CoreActual`, `Mzk1Chain2ContainerInterfaceActual`） | 仅**接口占位**，非 IUT 对象 |
| M2 C2.1 | **接口占位** | `qPilotRegion_subset_possibleImage` = data field（trivial） |
| M3 C2.2 | **接口占位** | `model_requirement_and_box` 是定义展开；无真实上箱 |
| M4 C2.3 | **接口占位** | `chain2_model_ssIneq` = `hmid.1`（trivial） |
| M5 数值 | BLOCKED：数据矛盾未裁定 | 见 §5 |
| M6 依赖 | LogLink/ThetaLink/Concrete/Tripod oleans 未产 | 见 §6 |

**trivial 标记（必须随文档保留）**：

- `qPilotRegion_subset_possibleImage` = **data field**（不是定理）。
- `chain2_model_ssIneq` = `hmid.1`（把 hypothesis 的 first conjunct 取出）。
- `g1_union_eq_single` = `rfl`（定义即相等，不是几何结论）。
- `pf_eq_unique_iso` / `scalingUnique` = **自由 Prop**（没有证明，只是字段/假设）。
- `qPilotOrd` **不进入体积式**：`shellVolume` 只依赖 `baseShell`/`allowedLower`/`logp`；q-pilot 的 ord 只是区间成员，triviality 来源之一。

## 5. 数据矛盾登记（p=11）

| 版本 | 数据 | base 量级 | 状态 |
|---|---|---|---|
| A892 注释 | `e=n=1, r=0` | `base approx 1.49` | **与 §9/§10 冲突** |
| A883/§9-§10 | `e=10, r=1, n=10` | `base approx 3.31` | 待 stepxi 裁定 |

- 当前 `CHAIN2-RESULTS/PHASE2` 两套数字不可同时使用；在 stepxi 给出统一裁定前，**不产生数值 verdict**。
- 需要同时统一：arch（`log(sqrt(2)π)=1.491303`；1.1394 撤回）、`c=0.15`、p=11 的 e/r/n、以及 multi-bad odd-place 的 model-only 假设。

## 6. 证据版本钉死

- **根 `Iut/` 树**：`rlf_unique` = `Iut/LogLink/Thm311Rest.lean:473`；`rlf_cocycle` = 479；`mem_rposOrbit_iff` = 491；`def rlfData` = 523；`Thm15v.unique` = 529；`scaling_iff` 定义在 `Iut/ThetaLink/Link.lean:206`（`Thm311Rest.lean:559` 是 usage `frobScale`）。
- **tmp 副本**：`rlf_unique` 在 tmp 副本的 `:427` **作废**，不得引用。
- 所有候选 lana 文件 olean **未产**；在 root build 完成并通过 gate 前，只是源级证据。

## 7. OPEN DECISION：上箱对象与目标

- `VolShell <= U` 在模型/单调性下只给 `req <= U`；它**不推出** lana 的 `SSIneq`。
- 因此链二当前是“**与 `req <= U` 等价**”，不是“与 `SSIneq` 等价”。把目标从 `req <= U` 改回 `SSIneq` 需要用户决策（OPEN DECISION）。
- 若要接 `SSIneq`，必须补的正是 `real_dictionary`：`qPilotRegion subset P ⇒ (s-1)A <= VolShell P`（或平均版）。

## 8. Owner 与下一步

| owner | 职责 | 下一步 |
|---|---|---|
| abc | 真实对象 C2.1-C2.3、`real_dictionary` 接口 | 冻结平均量词 + 写 `real_dictionary` 目标（不证明） |
| qpilot | 不再提供 G1 首选；给 G 的真实定义候选或明确说无 | 重新审 G 来源；G1 仅作 rlf 唯一性输入 |
| stepxi | 数值裁定 p=11 两套数据；重算 arch/G3 表 | 统一数据后回填 RESULTS/PHASE2 |
| hull | Θ-data 局部项/体积项 | 裁定 e/r/n 与 arch；提供 VolShell 实际公式 |
| shehdd | lana oleans/支持引理 | 编译 LogLink/ThetaLink/Concrete/Tripod 依赖 |
| mainline | 根树/build | 把依赖 oleans 接入 root build |
| stage4 | 审计 | 登记 trivial/自由 Prop/OPEN DECISION，禁止把模型当定理 |

## 9. 依赖 oleans（摘要）

| root | missing | key |
|---|---:|---|
| LogLink | 10/10 | `Thm311Rest`, `Thm311`, `Lattice`, `Local`, `Global`, `Kummer`, `Arch`, `Column`, `Split` |
| ThetaLink | 4/4 | `Link`, `Gauss`, `PrimeStrip`, `Wall` |
| Concrete | 45/51 | `Ind1Invariance`, `Container`, `LocalConstruct/{ScaleVolume,Prop14,LogShell,Hull,Volume}` |
| Tripod | 32/39 | `CyclicBound`, `CyclicIsogeny`, `Height`, `Core`, `Main` |
| ThetaData | 4 | `Basic`, `LocalConditions`, `LocalTateOfExistence`, `Orbicurve` |

所有 olean 未产；不得当 green。
