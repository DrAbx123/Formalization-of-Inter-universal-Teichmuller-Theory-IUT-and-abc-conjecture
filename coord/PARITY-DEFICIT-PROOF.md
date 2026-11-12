# PARITY-DEFICIT-PROOF — per-place/parity 形式的 gap 覆盖目标 (A1077)

| field | value |
|---|---|
| Status | PARTIAL (per-place/parity 分解 + Lean 骨架；per-p 估计与 large-m 限制已标 GAP) |
| 目标 | `M = V + gap − (sF−1)A ≥ 0` ⇔ `Σ_p [V_p + ind2_p − (sF−1)A_p] ≥ 0`（把 gap 分配为 ind2） |
| 数值输入 | qpilot: parity 分组 12,354/12,354 通过（有界 m 数据） |

## 1. gap 的 per-place 形式（与 lana 定义对齐）

lana `gapHullAt`（Gap:895-898）：
```
gapHullAt i vQ = sum_c tupleWeight vQ c * ind2Term D i p c     (vQ = finite p)
               = 0                                            (vQ = infinite)
```
且 `gapHullAt_nonneg`（Gap:937-940）。`gap`（Gap:502-527）满足
`gap = rhs + sF*A − V`，且按定义可写成
```
gap = (1/nC) * sum_i sum_vQ gapHullAt i vQ
    = (1/nC) * sum_i sum_p sum_c packetWeight * ind2Term
```
（`logVol` 的 procession/procession 平均与 packetVol 展开，Gap:916-935 `gapHullAt_eq`）。
于是逐 place：
```
V_p   := (1/nC) * sum_i hullPacket_i(p)                  （hull(vcI) 的逐位 packet 体积）
gap_p := (1/nC) * sum_i (sum_c packetWeight * ind2Term)   （= ind2_p）
A_p   := weight_p * qOrder_p * log p / (2l)               （q-side 逐位）
M     = sum_p [V_p + gap_p] − (sF−1) * sum_p A_p
      = sum_p [V_p + ind2_p − (sF−1)A_p]
```
⚠ 归一化注意：`A = Σ_p A_p`（无 1/nC），而 `V_p/gap_p` 带 1/nC（源自 procession 平均）；
逐位配对时按上式（A_p 与 V_p+gap_p 的系数已在 `(sF−1)` 处对齐）。

## 2. parity 分组充分条件

取 place 分组 `odd`, `even`（按素性/奇偶或任意 partition）：
```
ParityDeficit := (sum_{p in odd} (V_p + ind2_p) >= (sF−1) * sum_{p in odd} A_p)
              ∧ (sum_{p in even} (V_p + ind2_p) >= (sF−1) * sum_{p in even} A_p)
```
- 每个分组不等式是**严格强于**总目标的充分条件（两组合并 ⇒ 总目标）；
- 分组各自独立可验证（qpilot parity 12,354/12,354 通过 = 数值证据）；
- 更细分组（按素数、按 m 区间）同理。

Lean 骨架：
```lean
def PerPlaceDeficit {ι : Type*} (V ind2 A : ι → Real) (sF : Real) : Prop :=
  ∀ p, (sF - 1) * A p <= V p + ind2 p

theorem total_of_perPlace {ι : Type*} [Fintype ι]
    (V ind2 A : ι → Real) (sF : Real) (h : PerPlaceDeficit V ind2 A sF) :
    0 <= (∑ p, V p + ind2 p) - (sF - 1) * (∑ p, A p) := by
  have hsum : (∑ p, (sF - 1) * A p) <= ∑ p, (V p + ind2 p) :=
    Finset.sum_le_sum fun p _ => h p
  rw [Finset.sum_add_distrib] at hsum
  rw [← Finset.mul_sum] at hsum
  linarith

def ParityDeficit {ι : Type*} (odd even : Finset ι) (V ind2 A : ι → Real) (sF : Real) : Prop :=
  ((∑ p in odd, (V p + ind2 p)) >= (sF - 1) * (∑ p in odd, A p)) ∧
  ((∑ p in even, (V p + ind2 p)) >= (sF - 1) * (∑ p in even, A p))

theorem total_of_parity {ι : Type*} [Fintype ι] (odd even : Finset ι)
    (hpart : Disjoint odd even) (hcover : odd ∪ even = Finset.univ)
    (V ind2 A : ι → Real) (sF : Real) (h : ParityDeficit odd even V ind2 A sF) :
    0 <= (∑ p, V p + ind2 p) - (sF - 1) * (∑ p, A p) := by
  -- split sum over odd/even, then add the two hypotheses
  have hsum : (∑ p, (V p + ind2 p)) = (∑ p in odd, (V p + ind2 p)) + (∑ p in even, (V p + ind2 p)) := by
    rw [← Finset.sum_union hpart, hcover]
  have hA : (∑ p, A p) = (∑ p in odd, A p) + (∑ p in even, A p) := by
    rw [← Finset.sum_union hpart, hcover]
  rw [hsum, hA]
  linarith [h.1, h.2]
```

## 3. 使分组不等式成立所需的 per-p 估计

### (i) ind2 的 frac 下界（A1022）
```
ind2Term i p c >= frac(j²*m/(2l)) * log p - (3 + log e)      （rounding 修正）
```
⇒ `ind2_p >= frac_p * log p − K_p`（K_p = O(3+log e)）。

### (ii) V_p 的 tame 下界
```
V_p >= (1/nC) * sum_i sum_c packetWeight * (1 - 1/e) * log p − (shellDefect corrections)
```
（VcI:403-435 tame 公式；ramified 位可负，需要逐位 e 的界）。

### (iii) A_p 的结构
```
A_p = weight_p * qOrder_p * log p / (2l)
```
要 `(sF−1)A_p` 被 V_p+ind2_p 覆盖，需要 qOrder_p 的界或 ind2/V_p 含 m-线性正项——**这正是 A1022/A1035 的 large-m 问题**。

### (iv) parity 分组的作用
- 逐位条件 (i)-(iii) 若在 **有界 m** 下成立 ⇒ parity 分组通过（数值 12,354/12,354 对应此情形）；
- 对 **m 无界**：Σ_{odd} 的负线性项无法通过分组消除（总线性系数仍为负，见 A1035/A1030），
  故 parity 分组**不能**单独推出 large-m 的 variant。

## 4. 判定

1. per-place 形式 `Σ_p[V_p+ind2_p−(sF−1)A_p] ≥ 0` 与 `gapHullAt`/`ind2Term` 定义对齐（§1）；
2. parity 分组是**严格充分**、可独立验证的分解（各组数值通过）；
3. 但要得到一般 m：需要 per-p 的 (i) frac 下界 + (ii) tame 下界 + (iii) A_p 的界/正项；
   (i)/(ii) 是 bounded 项，无法抵消 (iii) 的 ∝m 行；⇒ **parity/per-place 只能覆盖有界 m 或作为
   有限枚举组织，不构成 large-m 证明**；
4. 若将 admissible 数据加上 m 的界（UB），则 parity 分组 + 逐位估计可证 variant（条件版）。

## 5. 结论与下一步

- 交付：per-place/parity 精确形式 + Lean 骨架（`PerPlaceDeficit`/`total_of_perPlace`/
  `ParityDeficit`/`total_of_parity`）；
- GAP：per-p frac/tame 估计（A1022/A1030 的局部形式）与 large-m（A1035）；
- 建议：把 parity 分组作为 **数值验证组织**（记录 12,354/12,354），不当作一般证明；
  一般情形仍需 Step (xi-d) 或显式 UB。