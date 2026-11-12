# RECODE-STRUCTURAL — 目标 M≥0 的对象层重编码 (A1084)

| field | value |
|---|---|
| Status | READ-ONLY (structural recoding; no compile) |
| 目标 | `M = V+gap−(sF−1)A ≥ 0` ⇔ `−A ≤ rhs`（A=|log q|, rhs=−|log Θ|） |
| 要点 | 把数值项之和重编码为**一个结构陈述**：存在一个保体积/正 determinant 的态射（或区域包含），使 log-volume 单调性一步给出目标 |

## 0. 两种坐标（必须选一种，不能混）

| 坐标 | 定义 | 目标对应的对象陈述 |
|---|---|---|
| **Haar/signed**（paper Step (xi-d) 用） | `signedLogVolume vol S = log (vol S)`；`vol = Haar` | `QPilotRegion ⊆ ThetaHullRegion`，且 `log vol q = −A`、`log vol θ = −R` |
| **negative-log**（我们的 QRegion 文件） | `logVol = −log μ` | `ThetaHullRegion ⊆ QPilotRegion`，且 `logVol q = −A`、`logVol θ = −R` |

本文以 **Haar/signed 为主**（与 `Mzk1SignedLogVolumeCor312Actual`、`XiEContainment`、S1422 det 一致）。

## 1. 重编码：对象/态射语言

### 1.1 区域包含版（最简）
```
（结构陈述）存在区域 QPilotRegion, ThetaHullRegion ⊆ Ω 使得
  (i)  QPilotRegion ⊆ ThetaHullRegion;
  (ii) log (Haar QPilotRegion) = −A;
  (iii) log (Haar ThetaHullRegion) = −R.
```
推导（一步 log 单调性）：
```
(i) ⇒ Haar q ≤ Haar θ（measure_mono）
    ⇒ log(Haar q) ≤ log(Haar θ)（Real.log_le_log，正性）
    ⇒ −A ≤ −R  （用 (ii)(iii)）。
```
即目标 `−A ≤ rhs = −R`。**所有数值项（V、gap、sF、packetWeight、ind2、arch、torsion）在对象层被
“吸收”为两个区域与两个 log-volume 识别**；不再逐项相加。

### 1.2 Determinant 态射版（paper Step (xi-d) 的精确形式）
```
（结构陈述）存在单位 G（det⊗M 归一化）、M > 0、以及
  (i)  distribHaarChar G = M;
  (ii) G • QPilotRegion ⊆ ThetaHullRegion;
  (iii) log(Haar QPilotRegion) = −A, log(Haar ThetaHullRegion) = −R.
```
推导：
```
(ii) ⇒ Haar(G • q) ≤ Haar θ
(S1422 detDataOfHull/hull_smul_unit, hchar) ⇒ Haar(G • q) = M·Haar q
⇒ M·Haar q ≤ Haar θ ⇒ Haar q ≤ Haar θ（M≥1）
⇒ log(Haar q) ≤ log(Haar θ) ⇒ −A ≤ −R。
```
这正是 Step (xi-d) 的“determinant + normalized log-volume + 区域比较”一體化。

## 2. 唯一需要构造的结构对象

**`QPilotThetaContainment`**（唯一对象）：
```
structure QPilotThetaContainment (Ω) where
  qRegion θRegion : Set Ω
  q_measurable : MeasurableSet qRegion
  θ_measurable : MeasurableSet θRegion
  q_finite : Haar qRegion < ⊤
  θ_finite : Haar θRegion < ⊤
  q_pos : 0 < Haar qRegion
  subset : qRegion ⊆ θRegion
  q_normalized : log (Haar qRegion).toReal = -A   -- A = |log q|
  θ_normalized : log (Haar θRegion).toReal = -R   -- R = |log Θ|
```
对象层性质只需：**包含（或 det 缩放包含）+ 两个归一化等式 + 正性/有限性**。
（如果改用 determinant 版：把 `subset` 换成 `G • qRegion ⊆ θRegion` + `hchar`。）

## 3. 已 green 的部分实现（对号入座）

| 组件 | 对应结构陈述的哪一部分 | 状态 |
|---|---|---|
| `Mzk1SignedLogVolumeCor312Actual.signedLogVolume_mono` / `signed_cor312_inequality` | 1.1 的推导（包含 ⇒ signed 不等式） | **green** |
| `Mzk1SignedLogVolumeCor312Actual.XiEContainment` | 1.1 的数据形状（subset+q_pos） | **green（结构）** |
| `LeanFormal...haarLogVolume_mono`（FinitePlaceIQHullInterface:68） | 1.1 的 Haar 单调性 | **green** |
| `Mzk1QPilotHaarBridgeActual.QPilotHaarRegionData` + bridge | 1.1 的 Option B 实例（volume_eq/theta_subset） | **green 骨架，GAP 数据** |
| `Mzk1QRegionInclusionActual`（negative-log 坐标） | 对应 1.1 的 θ⊆q 版本 | **green 骨架** |
| `Mzk1ContainAttemptActual` | 缩放包含（`scaledRegion`/mono） | **green 骨架，GAP 缩放元** |
| `S1422HDDDetActual.detDataOfHull` | 1.2 的 det 缩放律 | **green**（`hchar` 条件） |
| `S2807_thetaHullVolume_eq_haarRegion` | 1.1(iii) 的 theta 侧归一化 | **green** |
| `S1418HDDConsumerActual` det⊗M | 1.2 的簿记/global hull | **green** |

⇒ **数值/单调性/归一化工具均已 green**；唯一缺的是**结构对象本身**：
qRegion/θRegion 的显式构造 + 两条归一化等式（或 det 缩放包含 `G•q ⊆ θ` 与 `hchar`）。

## 4. Lean 签名草案

```lean
/-- Structural recoding of -A <= rhs: a single containment + normalization object. -/
structure QPilotThetaContainment (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (A R : Real) where
  qRegion : Set Ω
  θRegion : Set Ω
  q_measurable : MeasurableSet qRegion
  θ_measurable : MeasurableSet θRegion
  q_finite : μ qRegion < ⊤
  θ_finite : μ θRegion < ⊤
  q_pos : 0 < μ qRegion
  subset : qRegion ⊆ θRegion
  q_norm : Real.log (μ qRegion).toReal = -A
  θ_norm : Real.log (μ θRegion).toReal = -R

/-- One-step log-volume monotonicity: structural object ⇒ target. -/
theorem target_of_containment {Ω} [MeasurableSpace Ω] {μ : Measure Ω} {A R : Real}
    (D : QPilotThetaContainment Ω μ A R) : -A ≤ -R := by
  have hmono : μ D.qRegion ≤ μ D.θRegion := measure_mono D.subset
  have hq : 0 < (μ D.qRegion).toReal := by
    rw [ENNReal.toReal_pos_iff]; exact ⟨D.q_pos, ne_top_of_le_ne_top D.θ_finite.ne hmono⟩
  have hle : (μ D.qRegion).toReal ≤ (μ D.θRegion).toReal := ENNReal.toReal_mono D.θ_finite.ne hmono
  have hlog : Real.log (μ D.qRegion).toReal ≤ Real.log (μ D.θRegion).toReal := Real.log_le_log hq hle
  rw [D.q_norm, D.θ_norm] at hlog
  linarith

/-- Determinant-morphism version (paper Step (xi-d)). -/
structure QPilotThetaDetMorphism (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) (A R : Real) where
  G : Ωˣ
  M : Nat
  hM : 0 < M
  hchar : (MeasureTheory.distribHaarChar Ω G : ENNReal) = (M : ENNReal)
  qRegion θRegion : Set Ω
  subset_scaled : G • qRegion ⊆ θRegion
  q_norm : Real.log (μ qRegion).toReal = -A
  θ_norm : Real.log (μ θRegion).toReal = -R
  q_pos : 0 < μ qRegion
  θ_finite : μ θRegion < ⊤
  -- det law: μ (G • qRegion) = M * μ qRegion  (from S1422 detDataOfHull/hull_smul_unit)
  det_law : μ (G • qRegion) = (M : ENNReal) * μ qRegion

theorem target_of_detMorphism {Ω} [MeasurableSpace Ω] {μ : Measure Ω} {A R : Real}
    (D : QPilotThetaDetMorphism Ω μ A R) : -A ≤ -R := by
  -- μ(G•q) <= μθ; μ(G•q) = M μq; M>=1 => μq <= μθ; log monotone
  sorry -- 目标陈述草案（det_law + monotonicity + M>=1）
```

## 5. 结论

1. 目标可重编码为**一个结构陈述**：`QPilotThetaContainment`（区域包含 + 两条 log-volume 归一化）
   或 `QPilotThetaDetMorphism`（Step (xi-d) 的 det 缩放包含 + `hchar`）；
2. 两种版本都只需**一步** log 单调性即得目标；全部数值项（V/gap/sF/ind2/arch/torsion）
   被对象层吸收；
3. 我们已 green 的 `signed_cor312_inequality`/`haarLogVolume_mono`/`XiEContainment`/
   `QPilotHaarRegionData`/`detDataOfHull`/`S2807` 已实现该编码的**全部工具与数据接口**；
4. 唯一缺的是**结构对象自身的构造**：qRegion/θRegion + 两条归一化（或 `G•q ⊆ θ` + `hchar`）；
   这是 Step (xi-d) 的几何内容，与 A1056/A1074/A1077 的结论一致；
5. 一旦给出该对象，目标在 Lean 中是 **一行 measure_mono + Real.log_le_log**（如 §4 草案）。