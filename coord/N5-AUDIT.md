# N5-AUDIT — N5 装配文档巡检（A1043）

日期：2026-11-13。**Status: READ-ONLY AUDIT；不编译、不新增 Lean。**
对象：`coord/N5-ASSEMBLY-FEASIBILITY.md`、`coord/N5-STATEMENT.md`、`coord/OUR-COR312-ROUTE.md`、`coord/N5-ASSEMBLY-INVENTORY.md`。
标准：`coord/DECOMP-AUDIT-TEMPLATE.md`（A–F 要件、§2 清单）+ A986/A988（禁止手动编译，gate 由 watchdog/mainline 统一汇总）。

## 0. 目标方向（先固定）

lana 的 variant 定义（`Iut/Cor312/Statement`/`LeftHandSide`，文档引 `LeftHandSide:93`）：
```
Corollary312Variant X := X.qPilot.lhs <= X.rhsData.rhs
lhs = -absLogQ = -A
```
所以 paper-faithful N5 的方向是 **`rhs >= -A`（rhs 的下界 / R 的上界）**。

* `N5Statement D := -D.qPilot.absLogQ <= rhs`（N5-STATEMENT:102-103）——方向正确；
* `N5Weak D C := -A - C <= rhs`（:106-107）——比 N5 弱，只给 `M >= -C`，**不是** `M>=0`；
* `M := A - R = A + rhs`（R=−rhs），故 `N5 ⇔ M>=0`；`N5Weak C ⇔ M>=-C`。

## 1. 方向核对：N1–N4 是否支持 N5Weak？

| 节点 | 文档陈述 | 方向 | 能否给 `rhs >= -A`？ |
|---|---|---|---|
| N1 | `paperLHS <= paperRHS`（Q 抵消） | 上界比较（辅助） | 否，不含 rhs/A |
| N2 | `V <= paperBox`（`StepVDictionary`） | **V 的上界** | 否；上界不能反推 rhs 下界 |
| N3 | `sum(1-1/l)logp <= DExactWithArch` | D 的**下界** | 否，D 不是 rhs |
| N4 | `deficit<=0 ↔ (ssCoeff-cLana)A+arch-torsion<=diff` | 等价重写 | 否，只把 deficit 条件化 |
| N5 | `rhs >= -A` / `V+gap >= (sF-1)A` | **下界（目标）** | 这才是 N5；当前无证明 |

**结论：N2 是上界，不能当 N5 的下界；N1/N3/N4 也不产生 rhs 下界。** 方向不一致是真实缺口，
不是符号小错；必须补 determinant/log-volume 比较（N5-STATEMENT §3 P3）或等价的下界机制。

## 2. 逐文档判定

### 2.1 `N5-ASSEMBLY-FEASIBILITY.md` — **PASS（分析级）**

**理由**：
* 明确检查方向：N5Weak 是 rhs 的**下界**；S3034 `-V_C3 <= CTheta*A` 是 `-V_C3` 的**上界**，
  S3016 `thetaSigned <= CTheta*|stepV|` 是上界，S3017 是 height 上界；三者都不能给 rhs 下界；
* 明确指出 S3016 的 `identification`/`upper` 是**接口字段**，不是定理；`hheight` 是 S2921HeightLeProcessionPointwise，未证；
* 明确指出 `S3019MissingBridge` 未证；没有把上界当下降、没有把字段当证明；
* 文档自标 `READ-ONLY audit`，无 Lean/无编译主张，符合 A986/A988。

**小 caveat（不改变 PASS）**：line 4 把 `N5Weak` 直接写成 `rhs>=-A` 并说“same as Corollary312Variant”；
实际 `N5Weak C` 有误差 C，只有 `C=0` 才是 variant。建议改为 `N5Weak 0 = variant`；文中后续结论不受影响。

### 2.2 `N5-STATEMENT.md` — **PARTIAL（含一行 INVALID 代数）**

**正确部分**：
* N5 精确陈述 `rhs>=-A`，并给 `N5 ⇔ 0<=M`、`M=V+gap-(sF-1)A`（:22-29）；
* 明确指出 paper 几何核心 = Step (xi-d) determinant/log-volume 比较，以及 lana `lgp`（`V-sF*A`）
  与 paper q-pilot 区域（体积 `-A`）不能混用（:37-38, :58-63）；
* 最小子目标 `N5Weak C` 与 `n5_of_qPilotRegion_subset` 是**充分条件/计划**，没有冒充证明；
* `n5weak_implies_M_ge_negC` 方向正确（`M=A+rhs>=-C`）；`N5Statement` 用 `concreteVariantDataLit`，
  与 variant 的 lit 读法一致。

**INVALID 行**：
* line 27 写 `rhs = sF*A - V - gap`；由 `gap = rhs + sF*A - V` 反解应为
  `rhs = V + gap - sF*A`；原文多了一个负号（等于 `-rhs`）。
  这行若被用于推导会翻转方向，必须改为 `rhs = V + gap - sF*A`；
  但文档的 `N5 ⇔ V+gap >= (sF-1)A` 与 `M` 等价式本身是正确的（未依赖该错误行）。

**其余缺口**：
* `N1-N4 green` 的 gate 未给 watchdog/mainline 记录；按 A986/A988 只能写 PENDING-WATCHDOG；
* `n5_of_qPilotRegion_subset` 缺 `rhs = logVol(hull(thetaPilotLit))` 的桥（P3 只是计划，未证）；
* `concreteVariantDataLit` 与 paper variant 的 iv/lit 选择需显式（N5-STATEMENT 用 lit；`IND123` 指出
  `concreteVariantData` 用 iv）；这一点未在 N5-STATEMENT 中对照。

**判定**：**PARTIAL**；若把 line 27 当作已用等式，则相关推导 **INVALID**；不能进证据链。

### 2.3 `OUR-COR312-ROUTE.md` — **PARTIAL**

**正确部分**：
* 目标与 N5 方向写对：`M:=A-R>=0`，`A=logQ/(2l)`，`R=|log Theta|`；
* N1–N4 描述准确：N1 代数不等式、N2 V 上界、N3 D 下界、N4 deficit 等价；
* 明确指出 N5 是唯一实质 GAP，且 N2/N4 不能单独给 variant（:90-104, :131-141）；
* 声明不使用 lana `Corollary312Variant`/`SSIneq`/`ConcreteVariantData` 作前提（:6）——
  这是良好的非循环声明（但需在 Lean 依赖上核实，文档未给文件级证据）。

**缺口**：
* 多处标 `green`（N1–N4、组件表）但**没有 watchdog/mainline gate 记录**；按 A986/A988 只能标
  PENDING-WATCHDOG/条件；不能自行宣称 green；
* N2 的上界与 N3 的下界方向不同；文档虽承认 N5 缺，但没有明确写“N2 上界不能当 N5 下界”
  的方向声明；本审计 §1 补上；
* `M=A-R` 与 `R<=paperRHS` 的装配是**计划**（:120-128 的 theorem 草案含 `hassembly` 假设），
  不是已证；`hassembly` 本身把 N5 作为假设——若把它当定理就是 CIRCULAR；文档把它列为 GAP，
  所以目前是 PARTIAL，不是 CIRCULAR。

**判定：PARTIAL**（方向/缺口诚实；但 green 无 gate、N5 仍是假设，不能作结论）。

### 2.4 `N5-ASSEMBLY-INVENTORY.md` — **PARTIAL**

**正确部分**：
* 逐文件列签名/依赖，明确 `S3016CThetaUpperInterface` 的 `identification`/`upper` 是**字段**，
  不是定理；`S3017` 条件于 `hheight`；`S3019MissingBridge` 无 proof；`S3050QUnitIdentification` 是 Prop；
* 明确 N5 不在栈中（§4），并给出最小 lemma set（§3）；
* 没有把界面字段直接当证明；没有反向使用上界。

**问题**：
* 文档开头 line 6-7 写 `Olean TRUE for all files below`，但全文**未给 watchdog/mainline gate 引用**；
  按 A986/A988 这是自我 gate 声明，不能作为 PROVED/green 证据；应改为
  `PENDING-WATCHDOG / 引用 mainline gate 汇总`；
* `S3016CThetaUpperInterface.upper_bound` 是从字段 `upper` 得到的条件结论，文档已注明；但
  “usable exact algebra” 段落不能把接口字段当已实例化；
* S3014 的 volume 是任意输入，文档已明说没有 bridge；保持 PARTIAL。

**判定：PARTIAL**（库存内容准确；但 `Olean TRUE` 的 gate 声明无来源，需降级；不能进证据链）。

## 3. 专项检查

### (i) 上界当↓界用？
* `N5-ASSEMBLY-FEASIBILITY` **正确拦截**：S3034/S3016/S3017 全是上界，不能给 `rhs>=-A`；
* `N5-STATEMENT`/`OUR-COR312-ROUTE` 未把 N2 上界直接当 N5 下界；它们把 N5 列为缺失；
* **没有文档犯“上界当下降”的结论错误**；但 N5-STATEMENT line 27 的 `rhs=sF*A-V-gap` 若被使用
  会把方向翻转，属**一行 INVALID 代数**，必须修。

### (ii) 接口字段当证明？
* `N5-ASSEMBLY-FEASIBILITY` 和 `N5-ASSEMBLY-INVENTORY` 都明确指出 S3016 的 identification/upper、
  S3017 hheight、S3019 bridge 是字段/假设，不是定理；**没有把字段当证明**；
* `OUR-COR312-ROUTE` 的 `StepVDictionary` 也写成“条件于 three fields”，没有声称已填；
* 唯一风险是 `N5-STATEMENT` 表里把 S3016/S3017 标成 “green/partial” 时没有区分“接口字段”与“已实例化”；
  需要补 `FIELD-ASSUMED` 标注。

### (iii) 循环？
* `N5-STATEMENT` 的 `N5Statement` **就是 variant 目标**；`M_nonneg_of_N5` 是“假设 N5 ⇒ M≥0”的
  平凡蕴含，不构成证明；文档把它标为 N5，不是“已证 N5”，故不是 CIRCULAR；
* 若某处把 `n5weak_implies_M_ge_negC` 当作 `N5Weak` 的证明，则是把目标当假设，须标 CIRCULAR；
  当前文档未这样做（它把 N5Weak/P3 列为最小子目标/计划）；
* `OUR-COR312-ROUTE` 的 theorem 草案把 `hassembly` 作为显式假设；这是合法的条件定理骨架，
  但不能报告为无条件 variant；文档已注明 N5 GAP。

## 4. 判定汇总

| 文档 | 判定 | 核心问题 | 能否进证据链 |
|---|---|---|---|
| `N5-ASSEMBLY-FEASIBILITY` | **PASS（分析级）** | 正确识别上界/字段/方向；仅 N5Weak 命名小 caveat | 可作审计记录（非定理） |
| `N5-STATEMENT` | **PARTIAL（含 INVALID 行）** | line 27 `rhs` 符号错；N1–N4 green 无 gate；P3 未证；lit/iv 未对照 | 否 |
| `OUR-COR312-ROUTE` | **PARTIAL** | N5 是唯一 GAP 的定位正确；green 无 gate；N5 仍是假设 | 否（计划） |
| `N5-ASSEMBLY-INVENTORY` | **PARTIAL** | 字段/缺口盘点正确；`Olean TRUE` 无 gate 来源 | 否（库存） |

**无直接 CIRCULAR 证明**（没有文档把 N5/SSIneq 当已证前提去推 N5）；
但 `N5-STATEMENT` 的 line 27 是 **INVALID 代数**，必须修正后才能引用；
`N5-ASSEMBLY-FEASIBILITY` 是本轮唯一 PASS 的分析文档，可作为“上界不能当下界”的 gate 依据。

## 5. 修正/后续 gate

1. 修正 `N5-STATEMENT:27`：`rhs = V + gap - sF*A`（不是 `sF*A - V - gap`）；
2. `N5-STATEMENT` 的 `N5Statement` 必须注明 `concreteVariantDataLit` 的 lit 读法；若目标用
   `concreteVariantData`（iv），需另立 `N5Statement_iv`，不能混用；
3. 任何 `N1–N4 green` 只能写 `PENDING-WATCHDOG`/引用 mainline gate 汇总，不得自宣 green；
4. `N5-ASSEMBLY-INVENTORY` 的 `Olean TRUE` 改为 `PENDING-WATCHDOG`（无 gate 引用）；
5. 真正的 N5 下界必须来自 determinant/log-volume 比较（P3）或显式 `rhs>=-A` 假设；
   N2 的 V 上界、N3 的 D 下界、N4 的等价都不能替代它。
