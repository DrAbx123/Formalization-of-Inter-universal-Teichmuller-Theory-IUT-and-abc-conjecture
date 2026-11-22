# 任务 E memo：Ehrhart / 格多面体 / toric / Newton 多面体
能否精确计算 fractional-lattice scaled Θ hull 的 log-volume 与 qPilot region 比较

日期：2026-10-30。性质：research-only 判定 memo。未改任何既有 Lean 声明，未换 target。
目标（不变）：paper-faithful IUT III Cor 3.12 的 `-|log Θ| ≥ -|log q|`。

---

## 0. 结论（TL;DR）

| 工具 | 判定 | 一句话理由 |
|---|---|---|
| lattice polytope（paper hull 是否） | **拒绝** | paper 的 hull 按定义就是 `λ·O`（Remark 3.9.5(i)），是 torsor 元素，不是多面体；值群坐标下是无界正交体 |
| Ehrhart / 拟多项式 | **拒绝** | 计数 ≠ 加法特征；次数、整数性、t-伸缩三重不符（§3） |
| toric geometry / Bernstein–Kushnirenko 混合体积 | **拒绝** | 需要多单项式多项式系统 / section 环；Θ 值是单项（`q[2u]^{j²}`），没有 graded Rees 代数 |
| Newton 多面体 / tropical / max-plus | **部分接受，但非计算工具** | 唯一正确的"多面体"对象是 direct-product hull 的**坐标支撑函数**；凸化对它不可见 ⇒ Newton 多面体对 hull log 不可见（§4、§5-S4） |
| 精确算 hull log 的现成工具 | **已有且 actual** | Haar 归一化 + 加法公式 `-(∑ c) log p`：`arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic` |
| 与 qPilot region 的比较 | **已有且 actual（条件）** | 包含 + log-volume 单调性，不需任何体积/计数理论 |

**要点：** 这不是"Ehrhart 还没试"，而是 paper hull 的对象类型和 log-volume 的函子性质使这四个
工具**无处作用**：hull log 是值群上的**加法特征**（对指数向量线性），多面体/凸几何对它是**不可见**的。
真正的 exact 缺口在 **carrier（`q[2u]` / root stack）** 与 **label 权重 / 全局 V_bad 归一化**，
两者都不是体积问题。

---

## 1. 精确定义与 anchors

### 1.1 paper 侧（IUT III 原文；文件 `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt`）

* **holomorphic hull 的定义（Remark 3.9.5, (i)，行 7652–7680）**：
  `U` 相对紧时，其 hull 是**包含 `U` 的、形如 `H = λ·O` 的最小子集**，
  其中 `λ ∈ IQ((−))` 且**每个分量非零**；`O` 是 Proposition 3.1(ii) 的
  "local holomorphic integral structure"（在 IQ 的每个直和项上取整结构）。
  `U` 不相对紧时，hull 取整个 `IQ((−))`。
  ⇒ **hull 是"一个尺度的整结构"，由 λ 决定（模 `O^×`）**。
* **H ⊆ P（行 7682–7690）**：`P` = direct product regions，`H` = hulls，且 `H ⊆ P`
  （hull 是直积区域）。`φ(P) = ⋂_{H ⊇ P} H`（行 7702–7706）。
  ⇒ **hull 算子按分量独立：`φ(P)_v` 只由 `P_v` 决定，坐标之间不混合。**
* **log-volume（Prop 3.9, (i)，行 6839–6893）**：
  nonarchimedean 情形 `M(−)` = **非空紧开子集**（行 6851）；archimedean 情形是紧闭包（行 6875）。
  `μlog(O) = 0`，并按 **packet-normalization**：乘以 `p_v` 加 `−log(p_v)`（行 6858–6860）。
  **procession-normalization**：对 capsules 的积取**平均**（行 6888–6893）。
  全局：对各 v_Q **相加**，有限多个非零（行 6949–6952）。
* **论文自己的警告（Remark 3.1.1, (iii)，行 5471–5477）**：
  这些 log-volume 的加权和**一般不是某个通常意义测度的对数**的实倍数。
  `direct product region` = 每个直和项中紧、正测度子集的直积（行 5486–5491）。
* **Cor 3.12 的实际逻辑（行 10843–10848、10895–10898、10900–10903）**：
  `R_{≤−|log Θ|} := {λ ∈ R | λ ≤ −|log Θ|}`；
  `−|log Θ|` **按定义是 `1,◦U` 的（负）log-volume**；
  `−|log q|` 是 q-pilot 表示所给区域的 log-volume；
  由包含 `−|log q| ∈ R_{≤−|log Θ|}` **形式地**得到 `−|log q| ≤ −|log Θ|`；
  并称这是"计算 q-pilot log-volume 的两种 tautologically equivalent 方式"。
  ⇒ **不等式来自"区域包含 + log-volume 单调"这一形式步骤，不是来自把两边各算成多项式/体积。**
  这一步在 Lean 中正是 `arithmeticTupleNormalizedLogVolume_mono`。

### 1.2 project 侧（现有 actual/conditional 对象）

* `rootThetaRegion j = F(j²·c_root)·O_hol`，`rootThetaImageSet = ⋃_j rootThetaRegion j`，
  `rootThetaHull = closure(rootThetaImageSet)`
  —— `RootHullContainmentInequalityActual.lean:57-79`。
* `qPilotClassicalRegion = F(c_norm)·O_hol`，`qPilotClassicalLog = −(∑ c_norm) log p`，
  以及 `qPilotClassicalLog_le_rootThetaHullLog`（`hpos/hfin` 条件）
  —— 同上 `104-133`。
* paper 系数版本：`paperRootCoefficientFamily = order/(2l)`，`paperRootThetaHull`，
  `paperRootThetaFormulaLog = −(∑_v c)·log p`，精确缺口 = `data + hull_eq` 两字段
  —— `BadPlacePaperRootThetaHullActual.lean:36-80`。
* `F(c) = arithmeticTupleFractionalLattice`（各局部范数球的 `Z_p`-span，**分量为实指数**）
  —— `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceFractionalTensorLattice.lean:46-51`。
* `O_hol` = 积分闭包；`arithmeticTupleNormalizedLogVolume μ S = (1/D)(log μS − log μO)`
  —— `FinitePlaceNormalizedUnitScalingLogVolume.lean:77-98`。
* **精确公式（actual）**：`ArithmeticTuplePureFractionalScalingData c →`
  `mu_log((F c)·O_hol) = −(∑_i c_i)·log p` —— 同上 `:133-153, 379-390`。
* qPilot：`qPilotRegion = {tensorUnit}`（**单点**），`qPilotLogVolume = log ‖q‖`
  —— `QPilotObjectActual.lean:95-118`。
* `qPilotRootLabelRegion = thetaTensorScaledRegion(qPilotRootLabelCoefficient)`；
  其剩余精确目标 `FractionalTensorRegionNormBound` 是**逐点范数上界**，不是体积
  —— `S708QPilotRootLabelRegionNormActual.lean:44-78`。
* 全局目标（model 版）：`perBQPilotLog ≤ perBThetaHullLog` 加权求和
  —— `PaperLevelXiFTargetProofActual.lean:57-105`。
* procession 平均（= Prop 3.9(i) 的 average）—— `ProcessionNormalizedLogVolumeActual.lean:42-99`；
  `l*` 类、权重 `1/l*` —— `S694ThetaAverageNormalizationActual.lean:24-47`；
  `lStar l = (l−1)/2` —— `LeanFormal/IUT/Audit/Diagnostics/ConcreteThetaLegacy.lean:17`。
* **已证伪**：label-sum hull（把 hull 换成 `∑_j`）在 `q<1` 且 `∑j²>1` 下与比较矛盾
  —— `CorrectedHullCounterexampleActual.lean:52-80`；`AUDIT_LEDGER.md:8950`。
* `PaperSignedHull` 把"hull log = procession 平均"作为**字段** `hull_logVolume_eq_average`
  —— `tmp/sheaf/xif/PaperSignedHull.lean:53-71`。

---

## 2. Q1：paper hull 是否 lattice polytope？——**否**（5 条独立理由）

1. **定义层面**：每个 hull 都是 `λ·O`。`H` 是 `IQ^×/O^×` 下的 **torsor**（λ 的每个分量非零），
   不是某 `R^n` 里的有界多面体。多面体数据（顶点、体积、面数、格点数）**没有对应物**。
2. **结构层面**：`H ⊆ P`，hull 是 direct product region，故 `φ` **按分量独立**。
   多面体的核心是坐标之间的**凸混合**；这里没有混合。
3. **拓扑/测度层面**：nonarchimedean 下 `M(−)` 是**非空紧开集**，`λ·O` 是范数球之积，
   **完全不连通**；其像在值群坐标里是**正交体（上集）**，**无界**。
   有界格多面体才有有限 Ehrhart 计数/体积；这里连有界性都没有。
4. **论文自身**：Remark 3.1.1(iii) 明确说这些 log-volume 加权和"一般不是某测度的对数"，
   所以"体积"（Lebesgue/多面体体积）与 `μlog` 之间没有保持结构的桥梁。
5. **不可见性（可证）**：hull 只取**坐标方向**的极值（`|λ_v| = max_{u∈P_v}|u_v|`）。
   坐标投影是线性函数，在凸包上的极值在原点集取得 ⇒ **把指数集换成它的凸包（Newton 多面体）
   不改变 hull**。所以任何格多面体不变量（Ehrhart 多项式、混合体积、面结构）对 hull log **不可见**。
   见 §5-S4 的精确陈述。

**结论**：不是"paper hull 恰好不是格多面体"，而是**按定义就不可能是**；任何把它当多面体处理的
路线都会改变对象（换 target）。

---

## 3. Q2：Ehrhart / 拟多项式是否给有限 hull log？——**否**（4 条）

记 `D = finrank_{Q_p}` 的维数，`c` 为实指数向量。actual 定理给出

`μlog((F c)·O_hol) = −(∑_i c_i)·log p`，而 `μ((F c)·O_hol)/μ(O_hol) = p^{−D·∑c}`。

1. **计数 ≠ 特征**：Ehrhart 的 `L_P(t) = #(tP ∩ Z^n)` 是**格点计数**；这里的量是
   **紧开集上的 Haar 测度对数**，即值群上的**加法特征**。二者函数类型不同：
   `L_P` 取值在 ℕ，`μlog` 取值在 `R` 且是 `log p` 的有理倍数。
2. **次数不符**：Ehrhart 多项式次数 = `dim P`，首项系数 = 体积；而 `μlog` 对 `c` **恒为线性**，
   与 `D` 无关（`D` 只进归一化并抵消）。若它是某格多面体的 Ehrhart 多项式，只能是 `dim P ≤ 1`
   的线段，此时 Ehrhart 数据除"长度"外不含任何信息 —— 与已知的 `∑c` 完全相同，**没有增量**。
3. **整数性/无理性**：格多面体的 `L_P(t) ∈ ℕ`；而 `μlog = −(∑c) log p` 在 `∑c ≠ 0` 时是
   `log p` 的非零有理倍数，**无理**（`log p` 对素数 p 超越）。二者不可能相等。
   ⚠ Lean 状态：Mathlib **没有** `Irrational (Real.log p)`（实查 `irrational_log` 0 命中；
   `NumberTheory/Transcendental/Lindemann/` 只有 `AnalyticalPart.lean`，没有主定理）。
   故此条目前只能作为 paper-level 论证，**记为 exact gap，不用假引理**。
4. **t-伸缩不符**：若按 `S_t = F(t·c)·O_hol` 做伸缩类比，则
   `μ(S_t) = μ(O)·p^{−D t ∑c}`（**指数**，不是拟多项式），`μlog(S_t) = −t(∑c)log p`（一次）。
   Ehrhart 的两种读法（测度/计数、对数/多项式）都不落地。
5. **有限性来源不同**：paper 的有限性是 `hull ⊆ λ·O` + packet normalization
   （=`IQHullLogVolumeInterface.hull_logVolume_lt_top`，
   `SourceHullCompactnessReduction.lean:52-107`）；Ehrhart 的有限性是"有界多面体体积有限"。
   不能互相替代。compact open 的**点数本身是无限的**，"计数"在这里连有限都不成立。

---

## 4. Q3：能否 Lean 形式化？

* **已经 actual、且不需要 Ehrhart 的部分**：公式定理（`…fractionalLattice_mul_holomorphic`）、
  包含 + 单调性（`qPilotClassicalRegion_subset_rootHull` + `…_mono`）、
  procession 平均（`ProcessionNormalizedMonoAnalyticLogVolume`）。这些已足够表达 paper 的
  (xi-f) 形式步骤。
* **Mathlib 支持（实查）**：全库 `Polytope|mixedVolume|Ehrhart|latticePointCount` **0 命中**；
  `Geometry/Convex` 只有 `Cone/ConvexSpace/Hull/Set/Star`。任何 Ehrhart 形式化都要从零建
  （格多面体 + 计数 + 多项式性 + 互反律），与本目标无关。
* **唯一值得写的桥**（"凸化不可见"）精确陈述：

  ```lean
  -- 对有限非空指数集 s : Finset (ι → ℝ) 与坐标 i：
  theorem inf'_le_of_mem_convexHull (s : Finset (ι → ℝ)) (h : s.Nonempty) (i : ι)
      {x : ι → ℝ} (hx : x ∈ convexHull ℝ (s : Set (ι → ℝ))) :
      s.inf' h i ≤ x i
  -- 等价 ∀-形式：(∀ x ∈ convexHull ℝ s, r ≤ x i) ↔ (∀ y ∈ s, r ≤ y i)
  ```

  证明路线：`Convexity.convexHull_min`（`Mathlib/Geometry/Convex/Hull.lean:46`）
  + 半空间凸性 `{y | r ≤ y i}`。
* **未编译（如实记录）**：
  - 已确认环境可用：`lake env lean` 编译一个只 import `Mathlib.Geometry.Convex.Hull` 的
    平凡文件 **EXIT=0**（约 24s）。
  - 但上述引理**未通过编译**：2026 版 Mathlib 处于 `Convex`（`Analysis/Convex/Basic.lean:52`）
    ↔ `IsConvexSet`/`Convexity.convexHull`（`Geometry/Convex/Hull.lean`）**双 API 未桥接**状态
    （实查无 `Convex ↔ IsConvexSet` 桥引理）；`IsConvexSet` 版半空间/线性原像引理也未提供。
    第一次 `lean_auto.py repair` 超出 120s 工具时限；一次直接编译出现
    `failed to read …\Std\…\FilterMap.olean.private`（该文件实际存在，属并发/文件锁，非数学错误）。
  - 判定：**不值得为 no-go 记录去补 Mathlib 桥**。若 lead 需要硬证据，工作量约
    = 建 `Convex ↔ IsConvexSet` 桥 + `IsConvexSet` 半空间引理，属库工作，不是本 target 的缺口。

---

## 5. 具体对象 / 定理：应当使用的（按优先级）

**S1（精确值，actual）** `arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic`
（`FinitePlaceNormalizedUnitScalingLogVolume.lean:379-390`）：
`mu_log((F c)·O_hol) = −(∑_i c_i)·log p`，前提 `ArithmeticTuplePureFractionalScalingData c`。
这就是 paper 的 `μlog(λ·O) = −∑_v log|λ_v|`（packet-normalization）在项目载体上的实现，
**是精确等式，不是估计**。

**S2（比较，actual+条件）** `qPilotClassicalRegion_subset_rootHull` +
`arithmeticTupleNormalizedLogVolume_mono` ⇒ `qPilotClassicalLog ≤ rootThetaHullLog`。
这正是 paper (xi-f) 的"包含 ⇒ 不等式"形式步骤。

**S3（paper 归一化）** Prop 3.9(i)：packet（`×p_v ↦ −log p_v`）+ procession（**average**）。
项目对应 `ProcessionNormalizedMonoAnalyticLogVolume`。注意 `PaperSignedHull` 把
"hull log = average" 作为**字段**（未证），这也是 ledger 的 exact 缺口之一。

**S4（唯一正确的"多面体"对象 = 坐标支撑函数 / min-plus）**
对 direct product region `P = ∏_v P_v`，hull 的 λ 由
`|λ_v| = max_{u ∈ P_v} |u_v|`（等价 `val(λ_v) = min_{u∈P_v} val(u_v)`）唯一确定，
故 `φ(P) = ∏_v λ_v·O_v`，`μlog(φ(P)) = ∑_v log|λ_v|`。
这就是 `F(inf_j c^{(j)})`。它是 **max-plus（热带）线性**，不是凸几何；
它的"Newton 多面体"是**轴对齐盒子**；且由 §2(5)，**凸化不改变它**。
⇒ Newton 多面体在这里的唯一贡献是坐标极值，而坐标极值直接可算，无需多面体理论。

**S5（carrier）** paper 的 λ 分量必须是 `q[2u] = q[1u]^{1/(2l)}` 的值，
它活在 extension/root stack（`hodgeTwoLthRoot`），不在 completion：
completion 的值群是 `p^{(1/e_v)Z}`，未必含 `p^{−order/(2l)}`。
这与 `PaperRootHullFormulaGap` 的完成根障碍（S342）诊断一致。

---

## 6. 明确拒绝清单（逐项，含理由）

* **R1 lattice polytope / Ehrhart**：拒。对象类型不成立（§2），功能不符（§3）。
* **R2 toric geometry / Bernstein–Kushnirenko 混合体积**：拒。BKK 数的是多项式系统在
  `(C^*)^n` 的解数，输入是**多单项式**的 Newton 多面体；此处每个 Θ 量是**单项**
  `q[2u]^{j²}`，没有多项式系统、没有 section 环 / Rees 代数 / 除子线丛截面分次代数，
  `qPilotRegion` 甚至是**单点**。无适用对象。
* **R3 Newton 多面体 / tropical**：仅在"若干单项式之和"时经 max-plus 进入。
  当前 target 的 hull 是 **union/closure（坐标 min）**，不是 sum；label-sum 读法已被
  `CorrectedHullCounterexampleActual` 证伪。故 Newton 多面体即便写出来，对 hull log 也不可见。
* **R4 用 Ehrhart 给有限性**：拒。有限性来自 `hull ⊆ λ·O` + packet normalization（§3.5）。
* **R5 "分母 2l ⇒ 拟多项式周期 2l"**：拒。拟多项式需要"随 t 的计数"；此处 2l 只以
  **整除条件**出现：`data.order_eq : c_i · commonExponent = integerExponent_i`
  （`FinitePlaceNormalizedUnitScalingLogVolume.lean:145`）。它给出存在性条件，不产生 log 公式。

---

## 7. exact gap（本 memo 能确认的）

**G1（体积侧：不需要新工具）**
hull log 的公式侧已闭合为 `−(∑c)log p`（actual，需 scaling data）。
Ehrhart 路线**不能**减少这个缺口，也没有任何"待 Ehrhart 计算"的量。

**G2（carrier：真正的对象缺口）**
`PaperRootHullFormulaGap` 的 `hull_eq` 与 `data` 都要求 paper 系数 `order/(2l)` 的
**λ 是 `q[2u]` 值**；在 completion 载体上这是值群整除/元素存在问题（S342 诊断），
在 root/extension 载体上才可能。**这是对象层缺口，不是体积计算缺口。**

**G3（归一化 / 权重：纯有理算术缺口）**
若 `−|log Θ|` 取"S694 平均"读法（`l*` 类、权重 `1/l*`、每类系数 `j²/(2l)`），则每 b 的
系数为
  `(1/l*)·∑_{j=1}^{l*} j²/(2l) = (l+1)/24`
（核对：`lStar l = (l−1)/2`，`∑_{j=1}^{l*} j² = l*(l*+1)(2l*+1)/6`）。
该值在 `l=5,7,11,13,17,19` 时 <1，在 `l ≥ 23` 时 ≥1（l=29 时 = 1.25）。
因此：
  * 若 qPilot 侧每类系数为 1，则比较 `∑ j²/(2l) ≥ l*` ⟺ `(l+1)/24 ≥ 1` **在 l < 23 时失败**；
  * 若 `−|log Θ|` 改取 **hull（坐标 min，j=±1）**读法，系数 = `1/(2l)`，不等式对一切 l 成立。
⇒ **"paper Θ-pilot hull log" 缺口的数学内容是"取平均还是取 hull(min)"这一归一化选择 +
全局 V_bad 权重**，是一个**有理数算术 + 定义选择**问题。这与 ledger 的
"(l+1)/24 在 l=29 仍 >1、per-b 标量路线无效、需全局 V_bad procession-normalized qPilot"一致。
**Ehrhart/多面体对此完全无话可说。**

**G4（qPilot 侧：逐点范数，不是体积）**
`S708` 的 `FractionalTensorRegionNormBound` 是 `∀ x ∈ region, ‖x‖ ≤ p^{−N}` 型**逐点**界；
其正确工具是 tensor lattice 的值/范数计算（逐坐标 max）。

---

## 8. 未运行/未编译项（如实）

* 本文所有 paper 引文来自本地 corpus 文本（行号为该 txt 的行号），未做 PDF 级复核。
* 未编译任何新 Lean 声明；"凸化不可见"引理只给精确陈述与证明路线（§4）。
* `tools/lean_auto.py repair` 一次超 120s 工具时限；直接 `lake env lean` 一次出现
  `FilterMap.olean.private` 读取错误（文件存在，疑并发/锁），平凡文件复测 EXIT=0。
* 未改 `AUDIT_LEDGER.md`、`coord/STATE.md`、`coord/queue.md`；建议由集成者登记本 memo，
  并在 ledger 增加一条"Ehrhart/polytope 路线判定：拒绝（含 §7-G3 的 (l+1)/24 算术）"。

---

## 9. 给 lead 的一句话

Ehrhart / 格多面体 / toric / Newton 多面体路线：**全部拒绝**（paper hull 按 Remark 3.9.5(i)
就是 `λ·O`，log-volume 是值群上的加法特征、对指数线性，凸化对它不可见）；
hull log 已被 actual 公式 `−(∑c)log p` 钉死，比较已被"包含 + 单调"钉死；
真正剩的是 **carrier（root stack 上的 `q[2u]` λ）** 与 **归一化选择（hull-min 还是 l* 平均，
后者系数 `(l+1)/24`，l≥23 才 ≥1）** 两个 exact gap —— 都不是体积问题。
