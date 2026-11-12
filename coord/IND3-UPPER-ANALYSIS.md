# IND3-UPPER-ANALYSIS — Ind3 上界结论与 theta-hull 侧 `R ≤ A` 链 (A1110)

| field | value |
|---|---|
| Status | ANALYSIS (source-level; no Lean, no compile) |
| 结论 | Ind3 给的是 **上界/上半连续（upper semi）**：可能像值 `z ≤ w`（Ind3 迭代值），且 `sourceMultiradialLogVolume c ≤ ...(ind3 n c)` ——**方向是上界**。我们的目标需要 **下界** `rhs ≥ −A`；Ind3 的上界方向**不能**直接给出它。判 **C（对目标方向）**；A490 的 wall 等式给的是**无 gap 强等式**（且文件 olean=False，红），不是我们的弱版。 |

## 1. 资产清单与定理陈述（提取）

### 1.1 `Indet05RouteMultiradialClassActual`（olean=True）
```
routeMultiradial_ind3_logVolume_le (I) (n) (c) :
  sourceMultiradialLogVolume I (sourceMultiradialMap I c) ≤  (★ 上界方向)
    sourceMultiradialLogVolume I (sourceMultiradialMap I ((sourceStepXICore I).ind3 n c))

routeMultiradial_ind3_level (I) (n) (c) :
  sourceMultiradialLevel I (map (ind3 n c)) = sourceMultiradialLevel I (map c) + n

routeMultiradial_ind3_possibleImage_upper (I) (n) (c) (z) (hz : z ∈ possibleImage c) :
  ∃ w, w ∈ possibleImage (ind3 n c) ∧ z ≤ w        (★ 可能像的上半连续)
```
**方向**：base 的 log-volume/可能像值被 Ind3 迭代值**从上方**控制（`≤`）。

### 1.2 `Hull12Ob9BoundTransferActual`（olean=True）
```
hull12_upperBound_transfer (I) (n) (c) (B)
  (hB : ∀ w, w ∈ possibleImage (ind3 n c) → w ≤ B) :
  ∀ z, z ∈ possibleImage c → z ≤ B
```
**用途**：把 Ind3 迭代上的**上界**转回 base；仍是**上界**，不是下界。

### 1.3 `Hull08Ob9LogLinkActual` / `Hull10H7Ob9ConsumerActual` / `Indet06H7Ob9WiringActual`（olean=True）
```
hull_ob9_interface (In : HullOb9Inputs) (g) (n) :
  Cor312HullDetConclusion M In.hull.theta
  ∧ ind1/ind2 invariance
  ∧ sourceMultiradialLogVolume c ≤ sourceMultiradialLogVolume (ind3 n c)

hull10_h7ob9_consumer (In : HullH7Ob9ConsumerInputs) ... :
  Cor312HullDetConclusion M In.hull.theta ∧ ind1/ind2 invariance
  ∧ (可能像的上半连续)

h7Ob9_comparison_ind3_one_sided：Ind3 单侧（上界）比较
```
**注意**：`Cor312HullDetConclusion M In.hull.theta` 是**条件**（来自 `HullDetAssemblyInputs`），
不是无条件目标；且它的内容与我们的 `−A ≤ rhs` 不同（须核对 orientation）。

### 1.4 `A490WallThetaShiftAlignmentActual`（olean=**False**，红）
```
wall_thetaShift_logVol (A : EtaAlg D) (hW : Wall D A) (hS : A.ThetaShift) :
  ∀ h1 h2, ∃ S : Ind3 D, -(sFactor (nC D) * D.qPilot.absLogQ) + logVol D S.1
      = (concreteVariantData D).qPilot.lhs
wall_region_logVol_eq_qPilot (A) (hW) :
  ∃ U, IsAdelic U ∧ InHullOfImage U ∧ logVol D U = qPilot.lhs
```
**性质**：若 `qPilot.lhs = −A`，则 `logVol S = sF·A − A = (sF−1)A` ——这是**无 gap 强等式**
（`V = (sF−1)A` 型），属于被禁止的强版方向；且文件当前红（olearn=False），不能引用。

### 1.5 `S3139SourceMultiradialConsumerActual`（olean=True）
```
SourceMultiradialTargetInput / sourceMultiradialTargetInput / sourceMultiradialEtHTTarget
conclusion : ...（消费目标，非上界比较；需具体读结构字段）
```
可作为 `sourceMultiradialLogVolume` 的数据接口，但**不提供**到 `S2717ThetaHullLogVolume` 的桥。

## 2. 方向分析：Ind3 能否给 `R ≤ A` / `rhs ≥ −A`？

记 `rhs = logVol(ThetaHull)`（我们的 signed 量，负值）；目标 `rhs ≥ −A` 是 **下界**。
Ind3 提供：
```
(i)  possibleImage c 的值 ≤ possibleImage (ind3 n c) 的值；
(ii) sourceMultiradialLogVolume c ≤ sourceMultiradialLogVolume (ind3 n c)；
(iii) 若 ind3 迭代有上界 B，则 base 也有上界 B。
```
⇒ Ind3 是 **upper semi / 上界**工具；要得到 `rhs ≥ −A`（下界）需要：
```
(D1) 把 sourceMultiradialLogVolume 与 S2717ThetaHullLogVolume 的**方向**对齐；
(D2) 一个**下界**来源（不是 Ind3 的上界）：例如 signed containment（qRegion ⊆ hullRegion）、
     Step (xi-d) determinant、或 Cor 3.12 结论本身；
(D3) 如果反过来用 Ind3 的上界（例如上界 `rhs ≤ B`），只能得到 `−A ≤ −B` 型（上界方向），
     不是我们的下界目标。
```
**结论**：Ind3 的上界方向与我们的下界目标相反，不能单独给 `rhs ≥ −A`；判 **C（对目标）**。
（Ind3 可用于 lana 式的 upper-bound 链/Step V box 的 rhs 上界，但不是我们弱版证明义务。）

## 3. 需要的桥（GAP 清单）

```
(B1) sourceMultiradialLogVolume ↔ S2717ThetaHullLogVolume / actualC3LogShellTensorRegion：
     目前无定义等价/不等式定理（source multiradial 与 C3 tensor Haar 是不同构造）；
(B2) 方向桥：从 Ind3 的上界到我们的下界目标，缺一个反转引理
     （例如 `logVol(θ-hull) ≥ logVol(source image)` 型的包含关系）；
(B3) A490 的 wall 等式：olearn=False（红），且给强等式 `V=(sF−1)A` 型（禁止）；
(B4) HullDetAssemblyInputs 的条件消费：`Cor312HullDetConclusion` 是条件结论，
     需确认其 orientation 与我们的 `−A ≤ rhs` 一致；
(B5) S3139 的结论结构需与 theta-hull 量对齐（当前无桥）。
```

## 4. 判定汇总

| 资产/定理 | 方向 | 对目标的作用 |
|---|---|---|
| `routeMultiradial_ind3_logVolume_le` | 上界 (≤) | **C**：与下界目标相反 |
| `routeMultiradial_ind3_possibleImage_upper` | 上界（z≤w） | **C**：上界 |
| `hull12_upperBound_transfer` | 上界传递 | **C**：仍是上界 |
| `hull_ob9_interface` / `hull10_h7ob9_consumer` | 条件 Cor312 结论 + 上界 | 条件，不直接 |
| `A490WallThetaShift` | **强等式**（sF−1)A | 禁止方向，且红 |
| `S3139SourceMultiradialConsumer` | 数据接口 | 无桥 |

## 5. 结论与下一步

1. Ind3 全部结论都是**上界/上半连续**，不能给 `rhs ≥ −A` 的**下界**；判 **C（对目标）**；
2. A490 的 wall 等式给的是无 gap 强等式（`V=(sF−1)A` 型），属禁止方向，且文件 olean=False；
3. 若要复用 Ind3，必须补 (B1)(B2)：sourceMultiradial ↔ theta-hull 的定义桥 + 方向反转包含；
4. 建议：Ind3 只用于 lana 式 rhs 上界 / StepV box 的辅助，不进入我们弱版证明链；
   我们的下界仍走 signed containment / Step (xi-d) / StructuralTarget 路线。
5. 记录 GAP：GAP-IND3-BRIDGE (B1)(B2)；A490/RED 不引用。