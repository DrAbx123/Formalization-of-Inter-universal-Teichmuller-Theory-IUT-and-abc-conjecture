# STRUCTURAL-AUDIT — StructuralTarget/StructuralLineBundle 与 xi-d 结构审计（A1086）

日期：2026-11-13。**Status: READ-ONLY AUDIT；不编译、不新增 Lean。**
对象：`tmp/sheaf/xif/paper/Mzk1StructuralTargetActual.lean`（SHA16 `F7C7C6FD1F90869C`）、`Mzk1StructuralLineBundleActual.lean`（SHA16 `F8FB2E5E8C1E3F85`）；文档 `coord/STRUCTURAL-XID.md`、`coord/RECODE-STRUCTURAL.md`。
两文件当前 **ole=False**（无 watchdog gate 记录）⇒ 状态一律 PENDING-WATCHDOG，不能写 green/PROVED。

## 0. 核心结论

1. 两个 Lean 文件的**条件定理方向**基本正确（在各自坐标下），且没有假设目标；
2. 但“对象存在性=GAP”的标注**只对“实际 q/θ 对象”成立，对抽象结构本身不成立**：
   抽象 `QPilotThetaContainment` 可用 `qRegion=θRegion`、`A=R` 平凡满足；`QPilotThetaDetMorphism` 可用 `G=id,M=1,q=θ` 平凡满足；
   因此这些结构是**条件接口**，不能当“已构造/非空洞”的几何对象；
3. `Mzk1StructuralLineBundleActual` 的 `S1487FormCData` 是存在性 Prop，**可用 detBundle=qPilotLineBundle、A=R 空洞满足**；没有定理把 detBundle 连到 theta determinant、把 A/R 连到 paper 的幅值；条件结论是 vacuous；
4. `STRUCTURAL-XID` Form B 写 `theta_subset_q`，但未定义 `normLogVolume` 符号；在 Haar/signed 坐标（`log μ`）下正确包含是 `q⊆θ`，不是 `θ⊆q`；这是**方向错配/歧义**；`RECODE-STRUCTURAL` §0 已区分两坐标，但其结构同样可平凡满足。

## 1. Mzk1StructuralTargetActual 审计

### 1.1 定义与方向

```lean
structure QPilotThetaContainment (Ω) [MeasurableSpace Ω] (μ) (A R) where
  qRegion θRegion : Set Ω
  hq_fin : μ qRegion < ⊤; hθ_fin : μ θRegion < ⊤
  hq_pos : 0 < μ qRegion
  subset : qRegion ⊆ θRegion
  q_norm : -A = Real.log (μ qRegion).toReal
  θ_norm : -R = Real.log (μ θRegion).toReal
```

* 这是 **Haar/signed 坐标**：`-A = log μq`、`-R = log μθ`；
* `q⊆θ` ⇒ `μq≤μθ` ⇒ `log μq≤log μθ` ⇒ `-A≤-R`；
* `target_of_containment` 的证明正确：measure_mono + ENNReal.toReal_mono + log_le_log + 重写；**没有假设目标**；
* `QPilotThetaDetMorphism`：`G : Ω→Ω`, `M≥1`, `hchar : vol(G image q)=M*vol q`, `subset_scaled`, `hmono`, q_pos, q_norm/θ_norm；
  `target_of_detMorphism` 用 `vol q≤M*vol q≤vol(G image q)≤vol θ`，方向正确；
* 无 `sorry`/axiom（文本检查）；未编译 ⇒ PENDING。
### 1.2 “对象存在性=GAP”标注的问题

文件 header 写 **“existence of the objects = GAP-XID”**，但按结构本身：
* 任取一个正有限测度集 `S`，令 `qRegion=θRegion=S`、`A=R=-log μS`，
  则 `subset` 为 rfl、`q_norm/θ_norm` 成立、`hq_fin/hq_pos` 可满足；**抽象结构可平凡居住**；
* `QPilotThetaDetMorphism` 取 `G=id`、`M=1`、`q=θ`、`hchar` rfl 也可平凡居住；
* 因此 “no inhabitant” 只在**实际 Ω/μ/qRegion/θRegion**（及实际几何 identification）下才是 GAP；
  文件只给了抽象结构，没有字段强制实际 θ-hull/q-pilot 对象；
* 结论：`target_of_*` 是**条件恒等**，不是 xi-d 几何内容；`existence=GAP` 的标注应改为
  **“abstract structure is inhabited; actual-instantiation is GAP”**，并加非空洞性/strictness 字段。

### 1.3 判定

**PARTIAL**：定理方向正确、无循环；但 “对象存在性=GAP” 标注不精确，抽象对象可平凡构造；不能把结构当已构造的 q/θ 对象。
## 2. Mzk1StructuralLineBundleActual 审计

### 2.1 定义与方向

```lean
structure FormCLineBundleComparison (l) (K) where
  qBundle detBundle : LineBundle (k:=K)
  A R : Real
  hA : A = globalLogVolume qBundle / (2*l)
  hR : R = globalLogVolume detBundle / (2*l)
  hcmp : globalLogVolume detBundle ≤ globalLogVolume qBundle
```

`neg_A_le_neg_R`：`hcmp` + 正分母 ⇒ `R≤A` ⇒ `-A≤-R`；方向正确、条件定理。

### 2.2 空洞性（VACUOUS）

`FormCLineBundleComparison` 可由 `detBundle := qBundle`、`A:=R:=globalLogVolume q/(2l)` 满足：
* `hA/hR` rfl、`hcmp` rfl；目标变成 `-A≤-A`；
* `S1487FormCData` 是存在性 Prop：上述选择即给出 inhabitant；
* 但没有任何字段要求 `detBundle` 是 theta determinant line、或 `A/R` 是 paper 的 `|log q|/|log Θ|`；
  头注释承认 qPilotLineBundle 不是 theta determinant line，但结构本身没有强制；
* 因此 `S1487FormC_variant` 的“∃A R, -A≤-R”是空洞条件结论，不是 paper 的 `-A≤-R`；
* 这与 A1053 的 signed-stack 问题同型：条件对象/等价可在空洞处满足，不能当已构造。

### 2.3 判定

**PARTIAL/VACUOUS**：方向正确，但对象存在性不是有效 GAP 标注；`S1487FormCData` 可被 det=q 满足，缺非空洞性（actual det/theta line，A/R 的 paper 归一化）。
## 3. STRUCTURAL-XID / RECODE-STRUCTURAL 方向

### 3.1 STRUCTURAL-XID

* Form A（morphism）方向未定；Form C 草案 `comparison : det_logVol ≤ q_logVol -- or reversed/with constant` 太松，需固定；
* Form B 写：
  ```
  theta_subset_q : thetaRegion ⊆ qRegion
  vol_theta : normLogVolume thetaRegion = -R
  vol_q : normLogVolume qRegion = -A
  ```
  但 **`normLogVolume` 未定义**：若它 = `-log μ`，则 `theta⊆q` 正确；若它 = `log μ`（Haar/signed），正确包含是 `q⊆theta`。
  文档未固定坐标，和 `Mzk1StructuralTargetActual`（Haar: q⊆θ）方向相反；这是**方向歧义/错配**，
  应删掉 `-- or reversed` 式的松写法，固定 `normLogVolume` 与包含方向。
* Form B 还引用 `Mzk1QRegionInclusionActual`（negative-log, θ⊆q）与 `Mzk1XiEContainmentRequirementActual`（signed, q⊆hull），两者方向相反；并列时需分组。

### 3.2 RECODE-STRUCTURAL

* §0 的坐标表正确：Haar/signed `q⊆θ`，negative-log `θ⊆q`；
* 但 §2 的 `QPilotThetaContainment`/`QPilotThetaDetMorphism` 与 `Mzk1StructuralTargetActual` 一样，抽象可平凡满足；
  “唯一对象”不是自动 GAP，需 actual θ/q 对象与 strictness；
* §1.1 的公式 `q⊆θ ⇒ log μq≤log μθ ⇒ -A≤-R` 在 Haar/signed 下正确（只要 A=-logμq, R=-logμθ）；
* §1.2 的 det 版 `G scaled q⊆θ` + `hchar` 方向正确；但 `M≥1`/`hchar` 是字段，构造仍 GAP。
## 4. 判定汇总

| 对象 | 判定 | 说明 |
|---|---|---|
| `Mzk1StructuralTargetActual` | **PARTIAL** | 条件定理方向正确；抽象结构可平凡居住（q=θ/G=id），existence=GAP 标注不精确；未编译 |
| `Mzk1StructuralLineBundleActual` | **PARTIAL/VACUOUS** | `neg_A_le_neg_R` 条件正确；`S1487FormCData` 可 det=q 空洞满足；缺 actual det/theta 链接；未编译 |
| `STRUCTURAL-XID` Form B | **INVALID/歧义** | `theta_subset_q` 与 `normLogVolume` 未定义符号；Haar/signed 下应为 q⊆θ |
| `STRUCTURAL-XID` Form C | **PARTIAL** | det≤q 方向可用，但 “or reversed/with constant” 未固定；对象存在性 GAP |
| `RECODE-STRUCTURAL` | **PARTIAL** | 两坐标表正确；结构对象仍可平凡满足，需 actual/strict 字段 |

**总判定：无 CIRCULAR；但“对象存在性=GAP”不是充分标注——抽象结构是条件接口且可平凡居住。不得把 `target_of_containment`/`neg_A_le_neg_R`/`S1487FormC_variant` 当作 xi-d 对象已构造或 paper 不等式已证。**

## 5. 修正建议

1. `Mzk1StructuralTargetActual`：
   * 增加非空洞字段：`qRegion ≠ θRegion` 或 `μ qRegion < μ θRegion`（strict），并绑定 actual `thetaHullRegion`/`qPilotRegion`（如 S2807 的 region）；
   * 把 `hq_pos`/`q_norm` 与实际 `signedLogVolume`/`S2717` 读数连接；否则 q=θ 平凡满足；
   * header 改为 “abstract interface; actual instantiation = GAP-XID”。
2. `Mzk1StructuralLineBundleActual`：
   * `S1487FormCData` 增加字段：`detBundle` 等于 theta determinant line（S1422/S2807 侧），`A=...S2717...`、`R=...S2717Theta...`；
   * 禁止 det=q 空洞 witness（至少加 `detBundle ≠ qBundle` 或严格/实际 line 识别）；
   * `FormCLineBundleComparison` 的 `hcmp` 只能作为条件，不可报告“target PROVED”。
3. `STRUCTURAL-XID` Form B：固定 `normLogVolume := log μ`（Haar/signed）或 `-log μ`（negative-log），并相应改包含方向；删除 `-- or reversed`。
4. `RECODE-STRUCTURAL`：注明抽象结构可平凡满足，actual objects/strictness 才是 GAP；不要写“唯一对象”就暗示唯一/非空。
5. 两 Lean 文件无 olean（ole=False）⇒ watchdog/mainline 结果出来前一律 PENDING-WATCHDOG，不得写 green。