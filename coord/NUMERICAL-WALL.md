# NUMERICAL-WALL — NumericalWall / Wall / qPilot.lhs ≤ rhs (A1112)

| field | value |
|---|---|
| Status | ANALYSIS (source-level; no Lean, no compile) |
| 关键结论 | **我们的目标 `−A ≤ rhs` 正是 lana 的 `Corollary312Variant` / `NumericalWall`**（等价，非 SSIneq 强版）；`Wall` 是产生 U 的假设（`variant_of_wall`）；构造 U（adelic、InHullOfImage、`logVol U = qPilot.lhs = −A`）即可得目标 |

## 1. NumericalWall 的精确陈述（lana Checks）

```lean
-- tmp/sheaf/lana/iut/Iut/Wall/Checks.lean:56-57
def NumericalWall : Prop :=
  ∃ U : Region D, IsAdelic D U ∧ InHullOfImage D U ∧ (qVal D.bpsDegrees).eta (logVol D U) = etaQ D

-- Checks.lean:61-65: 影子引理（shadow lemma）
theorem numericalWall_iff : NumericalWall D ↔ Corollary312Variant (concreteVariantData D)
```
**解读**：`NumericalWall` = 存在一个 adelic 区域 U，落在**单个 (Ind1)-像**的 holomorphic hull 内，
且其 pointed map `R_val → R_ss` 等于 `η_q`（即 log-volume = `qPilot.lhs`）。
lana 的 `Checks` 注释（:11-20）明确指出：这是 (9-1) 的纯数值形式，**equivalent to Corollary 3.12 variant**，
因此在不知道 η^anab 来源时是**重述（circular）**。

## 2. A490 的约化（olean=False）

```lean
-- tmp/sheaf/xif/paper/A490NumericalWallRhsReductionActual.lean:17-19（当前 olean=False）
theorem numericalWall_iff_qPilot_le_rhs :
  NumericalWall D ↔ (concreteVariantData D).qPilot.lhs ≤ (concreteVariantData D).rhsData.rhs
theorem corollary312Variant_iff_qPilot_le_rhs :
  Corollary312Variant (concreteVariantData D) ↔ qPilot.lhs ≤ rhs
```
依赖：`hullActual_numericalWall_iff_exists_logVol`（hull 侧等价：存在 U ↔ `x ≤ rhs`）
与 `logVol_le_rhs`（hull 内 adelic 区域的 logVol ≤ rhs）；即：
```
NumericalWall ⇔ qPilot.lhs ≤ rhs
```
**A490 文件当前 olean=False**（自身失效）；其引用的 lana 依赖（`Iut/Wall/{Checks,EtaAlg,Rss,NumericalWallHullActual,Ind3,IdentifiedCopies}`）**当前全部 olean=False**（本 workspace 未编译 lana vendored 栈）——这是红的主因之一。

## 3. Wall / EtaAlg（EtaAlg.lean）

```
structure EtaAlg D（接口 T1-T3）：Hodge theaters；T1: Ind1/Ind2 在 S 上作用；
  T2: 只依赖 étale-unit 部分；T3: 输出是 adelic 区域且落在单个 Ind1-像的 hull 内；
def Wall (A : EtaAlg D) : Prop :=   -- (9-1)：对每个 Θ-link，存在 ι,S 使 η^anab_{ι,S} = η_q
  ∀ (Θ-link), ∃ (ι : B ≅ thetaBPS h₁) (S : Ind3), etaAnab A ι S = etaQ
theorem variant_of_wall (A : EtaAlg D) (hW : Wall D A) : Corollary312Variant (concreteVariantData D)
theorem etaAnab_eq_etaQ_iff : (9-1) ↔ log-vol(out ι S) = −|log q|
```
- `Wall` 是**假设/接口**（不是定理）：`variant_of_wall : Wall → Corollary312Variant`；
- lana 的 Faithfulness checks 表明：`∃ A, Wall D A ↔ variant`（interface 太弱，interface 的存在性即 variant）；
- 因此 `Wall` 只能在**给定具体 A**（Milestone 2–3 的 η-algorithm）时非循环使用。

## 4. 与我们的目标对齐（重要修正）

`qPilot.lhs` 的定义（lana LeftHandSide:81-93）：
```
qPilot.lhs = -absLogQ = -A
```
因此：
```
qPilot.lhs ≤ rhs  ⇔  -A ≤ rhs  ⇔  M ≥ 0（由 Mzk1GapBookkeepingActual.M_nonneg_iff）
```
**结论**：
- **我们的弱版目标 = lana 的 `Corollary312Variant` = `NumericalWall`（在 U 存在形式下）**；
- 强版是 `SSIneq`（`V − (sF−1)A ≥ 0` 型；`SSIneqOfStep3115Actual` 文档：SSIneq ⇒ variant 但 converse 不成立）；
- 先前 A1067 把 `Corollary312Variant` 与强版一起禁用，需**修正分类**：`Corollary312Variant`/`NumericalWall`
  是**目标等价物（不能作假设，circular）**，不是强版；SSIneq/`Corollary312Variant` 需分开标记；
- 使用时：不得假设 `Corollary312Variant`（= 目标），但可以复用其**等价改写/工具**（`numericalWall_iff`、`logVol_le_rhs`）
  作为 reducible 表述，只要不把它当已证输入。

## 5. 能否用我们已有 green 构造 U？

需要：U : Region D、`IsAdelic D U`、`InHullOfImage D U`、`logVol D U = qPilot.lhs = −A`。
现有资产：
| 资产 | 提供 | 缺 |
|---|---|---|
| `Mzk1N5WeakSkeletonActual` | `N5Weak(0) ⇔ −A ≤ rhs`（目标形式） | 不构造 U |
| `Indet05RouteMultiradialClassActual` | Ind1/2 不变、Ind3 上界（方向相反） | 不构造 U |
| `Hull12Ob9BoundTransferActual` | 上界传递 | 不构造 U |
| `Hull08Ob9LogLinkActual` | 条件 `Cor312HullDetConclusion` + Ind3 上界 | 不构造 U |
| `A490WallNumericalAlignmentActual`（olean=False） | `Wall ⇒ NumericalWall ⇒ variant` | 文件红 |
| lana `NumericalWallHullActual` | `hullActual_exists_adelic_inHullOfImage_logVol`（由 `x ≤ rhs` 构造 U） | **lana 依赖 olean=False**（当前不可用） |

**判定**：我们已有 green **不能**构造出我们的 U；U 的构造 = 把 `−A ≤ rhs` 转化为区域存在性的
几何步骤（等价于 Cor 3.12 本身）：在给定 `−A ≤ rhs` 后 U 可由 lana `exists_adelic` 构造，
但**反向**（构造 U ⇒ 目标）正是 `NumericalWall ⇒ variant`，需要 lana 的 `numericalWall_iff`（或其 hull 侧版本）。

## 6. Lean 签名草案

```lean
/-- NumericalWall-shaped target data (our version). -/
structure NumericalWallData where
  U : Type                 -- region carrier
  isAdelic : Prop
  inHullOfImage : Prop
  logVolU : Real
  qPilotLhs : Real
  eta_eq : (logVolU = qPilotLhs)   -- (9-1) numeric form: logVol U = -A
  hull_bound : logVolU ≤ rhs        -- from logVol_le_rhs (given U in hull)

/-- Numeric form: U with logVol = qPilot.lhs inside hull gives -A <= rhs. -/
theorem target_of_numericalWall {A rhs logVolU : Real}
    (hq : logVolU = -A) (hb : logVolU ≤ rhs) : -A ≤ rhs := by
  rw [← hq]; exact hb

/-- Wall (EtaAlg) implies the numerical wall; recorded as an assumption, never proved here. -/
def WallHypothesis : Prop := True   -- placeholder; concrete Wall D A is the lana interface
```

## 7. 结论与建议

1. `NumericalWall`、`Corollary312Variant`、`qPilot.lhs ≤ rhs`、我们的 `−A ≤ rhs` 是**同一条弱版目标**；
2. 强版是 `SSIneq`（`V ≥ (sF−1)A` 型），与上述不同（lana 自己文档：SSIneq ⇒ variant 但非反之）；
3. A1067 的禁用清单需修正：`Corollary312Variant`/`NumericalWall` 是**目标等价物**（禁止作假设以免循环），
   但**不是**强不等式；强版清单只保留 `SSIneq`/`SSIneqForm`/`SSIneqExplicit`/`Corollary312VariantHolds`（若其确为强形式）；
4. `Wall` 是接口假设：`variant_of_wall` 可复用，但 `Wall` 的**具体实例**（η-algorithm）未构造，
   且 `∃ A, Wall A` 等价于 variant（lana checks）⇒ 用 Wall 作前提是循环的，除非有具体 A；
5. 我们已有 green 不构造 U；但若接受 lana 的 hull 侧等价（`numericalWall_iff_qPilot_le_rhs`，A490 red 需重写），
   目标可化为**单条区域存在性**（U 的构造），这是 Step (xi-d) 的几何内容；
6. 建议：写一个 green 适配文件（但 lana vendored 栈当前 **olean=False**，需先编译/等待）；import lana `NumericalWallHullActual` + `Rss`，
   重新证明 `NumericalWall ↔ qPilot.lhs ≤ rhs`（A490 当前红，勿依赖），然后用 `Wall` 假设可条件推出；
   但必须标注 `Wall`/`Corollary312Variant` 为**目标等价物**，不能计入 green 证明。
7. GAP：GAP-U-CONSTRUCTION（唯一缺）；lana 依赖 olean 状态见下。