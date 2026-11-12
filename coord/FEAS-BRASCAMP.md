# FEAS-BRASCAMP — Brascamp–Lieb/Barthe/Borell/log-Sobolev 能否实例化我们的目标 (A1096)

| field | value |
|---|---|
| Status | ANALYSIS (no Lean; no compile) |
| 判定 | **C（不蕴含目标）+ B（重述）**：我们的比较是**单个线性映射/缩放**下的 Haar 测度比较，其变换是**精确**的 `|det|` 公式；Brascamp–Lieb 的非平凡内容在**多线性投影系统/函数**情形，单个映射时退化为等式，不能提供新的 gap 下界 |

## 1. 外部定理（LITERATURE）

### 1.1 Brascamp–Lieb（BL）
对满射线性映射 `B_i : ℝ^n → ℝ^{n_i}`、指数 `p_i`，满足**维数条件**
```
Σ_i n_i / p_i = n
```
有
```
∫ ∏_i f_i(B_i x) dx ≤ ∏_i ( ∫ f_i^{p_i} )^{1/p_i}
```
（Gaussian 为极值；Lieb 定理给出最优常数）。

### 1.2 Barthe
给出 BL 的**最优常数**与等式情形（多线性/多映射系统的精确常数）；
其常数本质是某 Gaussian 极值问题的值。

### 1.3 Borell–Brascamp–Lieb / Prékopa–Leindler
乘积测度下的 log-concave 函数的 Brunn–Minkowski 型不等式；
给出 `μ(λA + (1−λ)B)^{1/n} ≥ λ μ(A)^{1/n} + (1−λ)μ(B)^{1/n}` 型（Minkowski 组合的体积）。

### 1.4 log-Sobolev（LSI）
Gaussian/乘积测度下的熵-梯度不等式；对集合只给 concentration（`μ(A)μ(A^c)` 型）。

## 2. 我们的结构

- 环境空间 `Ω = ∏_v Ω_v`（有限位/arch 的局部域乘积），测度 `μ = ⊗ Haar_v`；
- 区域 = 局部格/log-shell 的 tensor 积 `∏_v S_v`（凸、乘积）；
- 我们需要的比较（例）：`μ(π(S))` vs `μ(S)`、`μ(qroot^{j²}·S)` vs `μ(S)`、
  以及 `V+gap−(sF−1)A ≥ 0` 的 log-volume 比较；
- 关键工具：局部域的**线性映射 Haar 变换公式**
```
μ(B • S) = |det B|_v^{?} * μ(S)      （精确；Archimedean: |det|；p-adic: |det|_p）
```
我们的 `componentVol_units_smul`、`ordp_qrootOf`（= qOrder/(2l·e_w)）、`S1422 detDataOfHull`
正是这个**精确**公式的实例（单映射/单位缩放）。

## 3. 判定（A/B/C）

| 子命题 | 类型 | 理由 |
|---|---|---|
| 单映射缩放 `μ(a•S) = |a|·μ(S)` | **B（重述）** | 就是 BL 在单映射、p=∞/特征函数时的等式；我们的 `componentVol_units_smul` 已实现 |
| 多投影系统 `π_i` 的 BL 不等式 | **C** | 我们只有单映射（det/scale），没有多线性投影系统的非平凡常数 |
| 用 j² 权重构造 BL 指数 `p_j`（使 `Σ n_j/p_j = n`） | **B/C** | 可形式上实例化（见 §4），但对角映射下 BL 等式化 ⇒ 无新信息 |
| Borell/Prékopa–Leindler | **C** | 它控制 Minkowski 组合；我们的 target 不是 Minkowski 组合 |
| log-Sobolev | **C** | 只给 concentration/熵界，不比较两个指定 hull 区域 |
| 用 BL 给 gap 下界 | **C** | gap 不是多线性投影系统的函数积分比较 |

**结论：BL/Barthe/Borell/LSI 对当前 target 判定为 C（不蕴含）；其单映射特例只是 B（重述精确缩放）。**

## 4. j² 权重的可能映射（为什么仍不产生新下界）

我们的恒等式 `Σ_{j=1..nC} j² = nC·sF`（`Mzk1ScalingNormalizationActual.sum_jsq_eq_nC_mul_sFactor`）
可用来设 BL 指数 `1/p_j = j² / Σ j²`（则维数条件自动成立），并取对角映射
`B_j = diag(qroot^{j²} 在 label j 方向)`；但：
- 对角系统下 BL 的 Gaussian 极值常数 = `∏_j |det B_j|^{...}`（精确），与直接用 `|det|` 公式相同；
- 因此 BL 不等式在此**成为等式**，不提供正的下界余量（no slack），也不产生 gap 的新信息；
- 这与我们已知结论一致：q-线性项已被 qScale 精确相消（`SYMBOLIC-INPUTS.md` §5）。

## 5. 可能的（弱）用途：组织估计而非下界

- Prékopa–Leindler 可用来证明**凸性/对数凹性**的辅助事实（如 log-shell 的凸组合体积），
  但不直接给 `−A ≤ rhs`；
- LSI 可用于证 concentration（若需要上界 `μ(θHull)` 的尾估计），是**辅助工具**，不是目标蕴含；
- 若把 target 换成“平均/熵”版本（非 paper 目标），BL 才可能非平凡；但这不是我们的 variant。

## 6. Lean 签名草案（记录 trivial instance，说明为何不增益）

```lean
/-- Single-map Haar scaling (already implemented by componentVol_units_smul). -/
def HaarScaleLaw (μ : Measure Ω) (a : Ωˣ) (S : Set Ω) (c : ENNReal) : Prop :=
  μ (a • S) = c * μ S

/-- BL for a single diagonal map is the Haar scaling law (equality, no slack). -/
theorem bl_single_map_is_scaling (μ : Measure Ω) (a : Ωˣ) (S : Set Ω) (c : ENNReal)
    (h : HaarScaleLaw μ a S c) : μ (a • S) = c * μ S := h

/-- The j^2-weighted BL instance reduces to the same scaling law (no new bound). -/
def JsqWeightedBLInstance (μ : Measure Ω) (a : Ωˣ) (S : Set Ω) : Prop :=
  HaarScaleLaw μ a S 1
```
（仅记录：BL 在单映射情形无内容；若将来需要多投影系统，必须新增多线性结构。）

## 7. 结论

1. **判定 C**：Brascamp–Lieb/Barthe/Borell/LSI 均**不蕴含**我们的 target `−A ≤ rhs`（gap 下界）；
2. 其单映射/对角特例 = Haar 精确缩放公式，是 **B（重述）**，我们已有（`componentVol_units_smul`、`S1422`、`ordp_qrootOf`）；
3. `j²` 权重可构造 BL 指数使维数条件成立，但对角映射下 BL 等式化 ⇒ 无新下界；
4. 若未来引入**多投影系统**（例如同时投影到多个 label/place 子空间）并需要非平凡常数，才可能重新评估为 A；
5. 当前不建议沿此路线作为 gap 下界来源；可保留 Prékopa–Leindler/LSI 作为辅助工具（凸性/尾估计），但不进入 green 证明链。