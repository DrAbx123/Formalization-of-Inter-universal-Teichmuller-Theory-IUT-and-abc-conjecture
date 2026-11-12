# LOGSUBMOD-TARGET — log-measure 次模工具与 target 分解 (A1090)

| field | value |
|---|---|
| Status | TOOL 落地（实数核心真证；measure 级为显式 additivity 条件）；target 分解为 PLAN |
| Lean | `tmp/sheaf/xif/paper/Mzk1LogMeasureSubmodularActual.lean`（未编译；无 sorry/axiom） |

## 1. 工具（已写）

```lean
theorem submodular_real (p a b q : Real) (hp : 0 < p) (hpa : p ≤ a) (hpb : p ≤ b)
    (hq : q = a + b - p) : p * q ≤ a * b
theorem log_submodular_real ... : Real.log p + Real.log q ≤ Real.log a + Real.log b
theorem log_submodular_of_measure (μ) {A B}
    (hinter_pos : 0 < (μ (A ∩ B)).toReal)
    (hinter_le_A : (μ (A ∩ B)).toReal ≤ (μ A).toReal)
    (hinter_le_B : (μ (A ∩ B)).toReal ≤ (μ B).toReal)
    (hadd : (μ (A ∪ B)).toReal = (μ A).toReal + (μ B).toReal - (μ (A ∩ B)).toReal) :
    Real.log ((μ (A∩B)).toReal) + Real.log ((μ (A∪B)).toReal) ≤ Real.log ((μ A).toReal) + Real.log ((μ B).toReal)
```
证明：`(a−p)(b−p) ≥0` ⇒ `p(a+b−p) ≤ ab`；log 由 `Real.log_le_log` + `Real.log_mul`。

## 2. 能否把 `V + gap − (sF−1)A` 写成区域和/交的 log-volume？

设 `X = ThetaHullRegion`（体积 μX），`Y = QPilotRegion`（体积 μY）；
目标 `−A ≤ rhs` 在 Haar 坐标下等价于 `μY ≤ μX`（若 `log μY=−A`, `log μX=−R`）。
次模不等式给出：
```
μ(X∩Y) · μ(X∪Y) ≤ μX · μY
⇔ log μ(X∩Y) + log μ(X∪Y) ≤ log μX + log μY
```
**用途**：若能把 `μ(X∩Y)`（或 `μ(X∪Y)`）与 `V/gap` 的 log-volume 组合对应，
则得到一个**非平凡下界**：例如若 `μ(X∩Y) ≥ μY`（即 Y⊆X），则不等式退化，
需要**非嵌套**区域（部分重叠）才能产生严格信息。

## 3. 嵌套 vs 非嵌套

- **嵌套**（X⊆Y 或 Y⊆X）：`X∩Y = min`、`X∪Y = max`，次模不等式变为**等式**
  （`μ(min)·μ(max) = μX·μY`），无新信息；
- **非嵌套**：`μ(X∩Y)·μ(X∪Y) < μX·μY` 可能严格，给出 geometric-mean 型约束；
  要把它接到 `V+gap−(sF−1)A`，需要把 `X∩Y`/`X∪Y` 的 log-volume 识别为 `V`、`gap`、`A` 的组合
  （**GAP-DECOMP**：目前没有这样的区域恒等式；V 与 gap 是不同的 procession/logVol 量，
  不一定来自两个区域的交/并）。

## 4. 具体候选分解（待验证）

1. `X = ThetaHull`（θ 的 hull），`Y = lgp^{-1}(QPilot)`（q-pilot 的归一化原像区域）；
   `X∩Y` 可能对应“θ-hull 与 q-pilot 的公共部分”，`X∪Y` 对应“并 hull”；
   其 log-volume 与 `V`、`gap` 的关系**未证**（GAP-DECOMP）；
2. 若 `X∪Y` 的 log-volume 可由 `V + gap` 控制（例如 `X∪Y ⊆ hull(...)` 型包含），
   则次模不等式给 `log μ(X∩Y) ≤ log μX + log μY − log μ(X∪Y)`，可能转化为 `gap` 下界；
3. 这与 Step (xi-d) 的 determinant 比较方向一致，但**不是同一构造**；若采用，需新增区域对应引理。

## 5. 结论

1. 次模工具（实数核心 + log 形式）**真证**落盘；measure 级需要一个 Real additivity 桥（GAP-MEAS-ADD）；
2. 我们的 target **不能**直接由次模不等式得到：V/gap 不是现成的两区域交/并 log-volume，
   需要新区域恒等式（GAP-DECOMP）；
3. 嵌套情形退化为等式（无信息），因此需要构造**非嵌套**区域对；
4. 若能在 Step (xi-d) 的 determinant 区域上找到 X,Y 使 `μ(X∩Y)` 与 `V+gap` 对应，
   次模不等式可给非平凡下界；这是后续候选路线。