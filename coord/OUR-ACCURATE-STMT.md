# OUR-ACCURATE-STMT — 我们自己的 Cor312 陈述与可证性判定 (A1121)

| field | value |
|---|---|
| Status | ANALYSIS + Lean 签名草案 (no compile) |
| 结论 | 我们的量（S2717/S2807/S2691）**不含 nC/j-average/sFactor/level 项** ⇒ 不受 lana 的 sF>1 张力影响。variant `M := A − R ≥ 0` 可由**两条基本事实**直接得到：(i) q 侧归一化 `A = −log μ(qRegion)`（即 `(μ qRegion).toReal = exp(−A)`）；(ii) `qRegion ⊆ θRegion`（Haar 单调性）。缺 (ii) 时不可平凡得；此时需 containment/det 比较（GAP）。 |

## 1. 我们自己的精确陈述

用现有定义（均为 Real）：
```
A := paperQAbsLog l logQ = qNormFactor l * logQ = logQ/(2l)    （S2691:55；= |log q|）
R := S2717ThetaHullLogVolume = -(haarLogVolume μ θRegion).toReal
     = -Real.log ((μ θRegion).toReal)                        （S2807:40-47）
μ := actualC3LogShellTensorHaar C3,  θRegion := actualC3LogShellTensorRegion C3
M := A - R = paperQAbsLog l logQ - S2717ThetaHullLogVolume
```
variant（我们的目标）：
```
M >= 0   ⇔   R <= A   ⇔   -|log Θ| >= -|log q|   （paper Cor 3.12 的 signed 形式）
```
注意：这里 `A`、`R` 都是**标量**，定义中**没有** nC、j-average、sFactor、level；
因此 lana 的 `sF = ℓ(ℓ+1)/12 > 1` 张力（及 NonDerivable 反例）**不直接作用于我们的陈述**。

## 2. 能否由基本不等式直接得 M ≥ 0？

展开：
```
M = A - R = A + Real.log ((μ θRegion).toReal)
若 q 侧归一化成立：A = -Real.log ((μ qRegion).toReal)（即 (μ qRegion).toReal = exp(-A)），
则  M = Real.log ((μ θRegion).toReal) - Real.log ((μ qRegion).toReal)
     = log( μθ / μq )
因此：  M >= 0  ⇔  (μ qRegion).toReal <= (μ θRegion).toReal  ⇔  μ qRegion <= μ θRegion.
```
**两条基本事实**：
```
(F1) q 侧归一化： (μ qRegion).toReal = Real.exp (-A)   （或 log 形式 A = -log μq）
(F2) 包含： qRegion ⊆ θRegion                                （⇒ measure_mono ⇒ μq ≤ μθ）
```
由 (F1)(F2)：
```
μq ≤ μθ ⇒ log(μq) ≤ log(μθ) ⇒ -A ≤ -R ⇒ M = A - R >= 0  ✓（真证，纯 Real.log/measure）
```
**哪些情形可能 R > A？**
```
- 若 qRegion ⊄ θRegion（θ-hull 比 q 区域小）⇒ 可能 μθ < μq ⇒ R > A；
- 若归一化不成立（A ≠ -log μq，例如 A 用了 logQ/(2l) 而 μq 未按 exp(-A) 归一化）
  ⇒ 数值上 R > A 完全可能；
- lana 的 iv 单 j 情形：θ-hull 只含单个 scaleElt·shell，可能过小 ⇒ R > A；
- 我们的 θRegion = actualC3LogShellTensorRegion（C3 tensor 积分区域）没有与 q 区域
  的包含关系定理，故不能排除 R > A。
```

## 3. 若不能平凡得，需要的核心不等式

```
(C1) q 侧归一化：A = -log ((μ qRegion).toReal)，其中 qRegion 是 q-pilot 的 C3 区域
     （或 A = -log Haar(qPilotRegion)，与 paperQAbsLog 一致）；
(C2) 区域包含：qRegion ⊆ θRegion（θRegion = actualC3LogShellTensorRegion）；
     或 determinant 归一化比较（Step (xi-d)）：G • qRegion ⊆ θRegion 且 μ(G•q)=M·μq；
(C3) 正性/有限性：(μ qRegion).toReal > 0、(μ θRegion).toReal < ⊤（C3 紧区域已给 lt_top）；
(C4) 若用 measure 版：μ qRegion ≤ μ θRegion ⇒ ENNReal.toReal_mono ⇒ Real.log_le_log。
```
**结论**：我们的 variant 的**全部实质内容**就是 (C1)+(C2)（或 det 版）；
不需要 sF、nC、j-average、level。与 lana 的 strong SSIneq 无关。

## 4. Lean 签名草案

```lean
/-- Our scalar A = paperQAbsLog l logQ (= logQ/(2l)). -/
def ATarget (l : PrimeGeFive) (logQ : Real) : Real := paperQAbsLog l logQ

/-- Our scalar R = S2717ThetaHullLogVolume = -log (mu thetaRegion). -/
def RTarget {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θRegion : Set Ω) : Real :=
  - Real.log ((μ θRegion).toReal)

/-- Variant: M = A - R >= 0. -/
def MTarget (l : PrimeGeFive) (logQ : Real)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θRegion : Set Ω) : Real :=
  ATarget l logQ - RTarget μ θRegion

/-- (F1)+(F2) => M >= 0. -/
theorem MTarget_nonneg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {l : PrimeGeFive} {logQ A : Real} {qRegion θRegion : Set Ω}
    (hA : A = paperQAbsLog l logQ)                       -- A 的定义
    (hq : (μ qRegion).toReal = Real.exp (-A))             -- (F1) q 侧归一化
    (hsub : qRegion ⊆ θRegion)                            -- (F2) 包含
    (hqpos : 0 < (μ qRegion).toReal)
    (hθfin : μ θRegion < ⊤) :
    0 ≤ A - (- Real.log ((μ θRegion).toReal)) := by
  have hmono : μ qRegion ≤ μ θRegion := measure_mono hsub
  have hle : (μ qRegion).toReal ≤ (μ θRegion).toReal :=
    ENNReal.toReal_mono hθfin.ne hmono
  have hlog : Real.log ((μ qRegion).toReal) ≤ Real.log ((μ θRegion).toReal) :=
    Real.log_le_log hqpos hle
  rw [hq] at hlog
  have : -A ≤ Real.log ((μ θRegion).toReal) := by
    have hmem : Real.log (Real.exp (-A)) = -A := Real.log_exp (-A)
    linarith [hlog, hmem]
  linarith
```
（注意 `Real.log_exp` 的具体名称/方向需在实现时核对；此处为签名草案。）

## 5. 判定

| 问题 | 答案 |
|---|---|
| 我们的陈述是否依赖 sF/nC/j-average/level？ | **否**（S2717/S2807 无这些项） |
| 能否由基本不等式直接 M≥0？ | **能，若 (F1)+(F2)**；否则不能 |
| R>A 的可能情形 | qRegion ⊄ θRegion；归一化不成立；iv 单 j θ-hull 过小；C3 区域无包含定理 |
| 需要什么 | (C1) 归一化 + (C2) 包含（或 det 版）；正性/有限性辅助 |
| 与 lana 强版关系 | 我们的 M = A − R 是 paper signed 形式；**不涉及** SSIneq/`V≥(sF−1)A` |

## 6. 结论

1. 我们的 variant 精确为 `M = paperQAbsLog l logQ − S2717ThetaHullLogVolume ≥ 0`（等价 `R ≤ A`）；
2. 定义中没有 nC/j-average/sFactor/level ⇒ 不受 lana sF>1 张力影响；
3. 由 (F1) q 侧归一化 `μq = exp(−A)` + (F2) `qRegion ⊆ θRegion`，
   `measure_mono + toReal_mono + Real.log_le_log` 即得 M≥0（真证模板见 §4）；
4. 不能平凡得的情形 = 缺 (F1) 或 (F2)；此时 R>A 可能（θ-hull 过小/归一化不匹配/iv），
   需要的核心不等式正是 containment 或 determinant 归一化比较（Step (xi-d)）；
5. 下一步：把 (F1)(F2) 的实例化（qRegion/θRegion 的构造与归一化）形式化
   ——即 A1059/A1085 的 QPilotHaarRegionData/StructuralTarget 路线，但用我们**不含 sF**的定义。