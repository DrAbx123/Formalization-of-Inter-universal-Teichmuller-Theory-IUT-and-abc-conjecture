# DECOMP-NORMALIZATION — 逐行钉死 M 分解的 1/nC 与权重 (A1008)

| field | value |
|---|---|
| Status | PARTIAL (归一化推导完成；逐位展开唯一确定，候选不等式仍 OPEN) |
| 目标 | `M = A - R >= 0`，`A = |log q| = absLogQ`，`R = |log Theta| = -rhs` |
| 结论 | qpilot 的 `T/nC`（每 capsule 除以 nC）是**正确**归一化；不除 T 是重复计数 |
| 版本钉住 | lana 根 `Iut/` 树 + 行号；未手动编译 |

## 1. `A`：无 1/nC，只有 (1/2l) 和 place weight

lana `Iut/Cor312/LeftHandSide.lean:81-84`:
```
logQ := sum_{w in Q.badFinset.attach} Q.weight w * (D.qOrder w (Q.mem_bad w) : Real)
          * Real.log (residueChar w)
```
`:88`: `absLogQ := Q.logQ / (2 * (D.l : Real))`。

因此：
- `A := absLogQ = logQ/(2l)`；**没有对 capsules 的求和，也没有 1/nC**；
- 逐位 `A_v = weight_v * ord_v(q_v) * log p_v / (2l)`（`weight_v = Q.weight`，place weight）；
- 恒等式 `A = sum_v A_v`（线性，无 nC 因子）；
- place weight 的归一化在 `Q.weight` 内（`sum_w weight_w = 1` 口径），与 procession 的 nC 平均是两个独立操作（LogVolume:200-206 明言 procession 平均与 packet/Haar 归一化不同）。

## 2. `V` 与 `gap`：1/nC 来自 procession 平均

lana `Iut/WallEquiv/VcI.lean:741-744`:
```
logVol_hull_vcI_eq : logVol D (hullOf D (vcI D))
  = (sum i : Fin (nC D), sum^fin vQ, hullPacket D i vQ) / nC D
```
即 `V = logVol(hull(vcI)) = (1/nC) * sum_i sum_v hullPacket_i(v)`；`nC D = D.proc.length`
（LogVolume:207-209 的除以 `D.proc.length`；数值上 `nC = l* = (l-1)/2`）。

lana `Iut/WallEquiv/Gap.lean:895-898`:
```
gapHullAt i : RationalPlace -> R
  | .finite p => sum_{c : Lab i -> Fiber p} tupleWeight p c * ind2Term D i p c
  | .infinite => 0
```
这是**每 capsule i 的局部 gap 项**；因此 gap 的层级与 V 相同：
`gap = (1/nC) * sum_i sum_v gapHullAt_i(v)`（每 capsule 的局部项带 1/nC；参见 Gap:514 `gap` 定义处与 `gapHullAt` 的 sum 关系）。
若把每个 capsule 的局部 gap 直接相加而不再除 nC，就重复计数 nC 次。

## 3. `rhs` 的逐层归一化：唯一 1/nC 在 processionVol，label 权重在 packetWeight

`Iut/Cor312/RightHandSide.lean:107`: `rhs := R.vol.processionVol R.thetaHull`，
文档 :102-107 明言 `rhs = -|log(Theta)|`（signed）；故 `R = |log Theta| = -rhs`。

层级：
1. `processionVol R := (sum i, globalVol (R i)) / D.proc.length`（LogVolume:207-209）
   → **唯一 1/nC 在这一层**；
2. `globalVol (R i) := sum^fin vQ, packetVol i vQ (R i).region vQ`（LogVolume:177-178）
   → 无额外归一化（finsum，无 1/nC）；
3. `packetVol_product`（LogVolume:130-133）：
   `packetVol i vQ (productRegion U) = sum_c, (prod j, weight vQ (c j)) * componentVol i vQ c (U c)`
   → 只有 place weight 之积 `packetWeight i vQ c := prod j, weight vQ (c j)`（:141），
     **没有 1/nC、没有 1/l 因子**；`packetWeight_pos`（:153）。

结论：`rhs = (1/nC) * sum_i sum_v sum_c packetWeight i v c * componentVol i v c`。
每项的 1/nC 来自最外层 procession 平均；label 权重位置在 packetWeight；componentVol 本身不再除任何 nC。

## 4. `M = A - R` 的唯一正确逐位展开

由 `rhs = -R`：
```
M = A - R = A + rhs
  = A + (1/nC) * sum_i sum_v sum_c packetWeight(i,v,c) * componentVol(i,v,c)
```
这是**唯一**正确展开（A 侧无 1/nC；R 侧的 1/nC 在 procession 平均；componentVol 无额外归一化）。

在逐 capsule 形式下：令 `H_i := sum_v sum_c packetWeight * componentVol(i,v,c)`（每 capsule 的
局部项，可正可负），则
```
M = A + (1/nC) * sum_i H_i = (1/nC) * sum_i (A + H_i).
```
注意 `(1/nC)*sum_i (A + H_i) = A + (1/nC)*sum_i H_i`：A 只被计一次（nC 个 A/nC 之和 = A）。
若把 `H_i` 的负项（q-scaling T）不除 nC 而直接 sum，则得到 `A + sum_i H_i = A - nC*T`，
**重复计数 nC 次**——这正是 qpilot「不除 T 时余 1 个 admissible 负项」的来源。

## 5. 裁定 qpilot 的两种归一化

- **正确**：每个 capsuale 的局部负项 `T`（q-scaling）在 M 展开中带 `1/nC`（等价地，
  `H_i` 含 `-T`，外层除以 nC）；对全称 sum 后 q 侧总贡献恰为 `-T`（若各 capsule 同 T）。
  即 qpilot 的 `T/nC`（per capsule）正确；不除 T 的版本把 nC 份 T 全加上，过强且不符 lana 源。
- **错误**：把 T 当作已总化量再在 sum_i 外层不除 nC；这等于把 R 的 procession 平均去掉，
  与 `logVol_hull_vcI_eq`（VcI:741）不符。

## 6. Lean 陈述草案（未编译）

```lean
/-- nC(l) = (l-1)/2 (capsule count). -/
def nC (l : ℕ) : ℕ := (l - 1) / 2

/-- A has NO 1/nC: A = logQ/(2l). -/
def absLogQOf (logQ : ℝ) (l : ℕ) : ℝ := logQ / (2 * (l : ℝ))

/-- rhs is the procession average of capsule global sums. -/
def processionVol (H : Fin (nC l) → ℝ) : ℝ := (∑ i, H i) / (nC l : ℝ)

/-- M = A + rhs (rhs = -|log Theta|). -/
def MOf (H : Fin (nC l) → ℝ) (A : ℝ) : ℝ := A + processionVol H

/-- Per-capsule sufficient form. -/
def PerCapsuleBound (A : ℝ) (H : Fin (nC l) → ℝ) : Prop := ∀ i, 0 ≤ A + H i

/-- (1/nC) Σ_i (A + H_i) = A + (1/nC) Σ_i H_i. -/
theorem M_eq_avg (H : Fin (nC l) → ℝ) (A : ℝ) :
    A + (∑ i, H i) / (nC l : ℝ) = (∑ i, A + H i) / (nC l : ℝ) := by
  field_simp
  ring

theorem M_nonneg_of_perCapsule (H : Fin (nC l) → ℝ) (A : ℝ)
    (h : PerCapsuleBound A H) (hn : 0 < nC l) : 0 ≤ MOf H A := by
  unfold MOf processionVol PerCapsuleBound at *
  have hsum : 0 ≤ ∑ i, (A + H i) := Finset.sum_nonneg fun i _ => h i
  have := div_nonneg hsum (le_of_lt (by exact_mod_cast hn))
  linarith
```

## 7. 结论

1. A 无 1/nC，`A = Σ_v A_v = logQ/(2l)`；
2. V、gap、rhs 都带 1/nC，源自 procession 平均（VcI:741、Gap:895 局部项、LogVolume:207）；
3. rhs 逐层：processionVol（唯一 1/nC）→ globalVol（无）→ packetVol_product（place weight，无 1/nC）；
4. 唯一正确展开 `M = A + (1/nC)Σ_iΣ_vΣ_c packetWeight·componentVol`；
5. qpilot 的 `T/nC` per capsule 正确，不除 T 的归一化错误（重复计数）；
6. 逐 capsule 充分条件 `∀ i, 0 ≤ A + H_i` 足以推出 `M ≥ 0`（A 只计一次）；
7. 未写任何 Lean 编译；恒等式/展开待 watchdog 编译，候选不等式仍 OPEN。