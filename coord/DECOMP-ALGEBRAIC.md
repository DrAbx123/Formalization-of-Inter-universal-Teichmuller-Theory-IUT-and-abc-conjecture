# DECOMP-ALGEBRAIC — 纯代数分解：Σj²=nC·sF 与 frac/floor (A1034)

| field | value |
|---|---|
| Status | **DECISION: 纯代数恒等式 `M = log p * [(1 - sF)*x_1 + mean(frac_j)] + Kbar`；floor/frac 项有界（≤log p），权重拆分无法改变总系数 sF>1 ⇒ 代数上无法抵消负线性项；需正线性项或 UB** |
| 输入 | A = m logp/(2l)；x_j := j²m/(2l) = j²*x_1；x_1 = m/(2l)；Σ_{j=1..nC} j² = nC*sF（green `Mzk1ScalingNormalizationActual.sum_jsq_eq_nC_mul_sFactor`） |

## 1. 记号与基本恒等式

```
A       = m * logp / (2l)              = x_1 * logp,      x_1 := m/(2l)
qScale_j = j^2 * A                     = x_j * logp,      x_j := j^2 * x_1
Σ_{j=1..nC} j^2 = nC * sF              (green)
```

## 2. M 的逐 j 重排

由 `M = A + rhs`（rhs = −R = −|logΘ|），rhs 的逐 capsule 展开取线性部分
`rhs_lin = (1/nC) Σ_i (−x_{j_i} logp)`；procession 平均用 `Σ_i j_i² = nC*sF`：
```
(1/nC) Σ_i x_{j_i} = (1/nC) Σ_i j_i^2 * x_1 = sF * x_1
```
故（线性+frac 分离前）：
```
M = logp * x_1 - logp * (1/nC)Σ_i x_{j_i} + Kbar
  = logp * x_1 * (1 - sF) + Kbar,           (Kbar = tame/arch/ind2 等)
```

## 3. floor/frac 分解

rounding（leastHull 的整数格）把 qScale 的 x_j 换成整数 `n_j`（floor 或 ceil）：
```
n_j = floor(x_j)  (或 ceil(x_j) = floor(x_j)+1)
x_j = n_j + frac(x_j),      0 <= frac(x_j) < 1
(1/nC) Σ_j n_j = (1/nC) Σ_j (x_j - frac(x_j)) = sF*x_1 - mean(frac)
```
代回（线性部分）：
```
M = logp * [x_1 - (1/nC)Σ_j n_j] + Kbar'
  = logp * [x_1 - sF*x_1 + mean(frac)] + Kbar'
  = logp * [(1 - sF)*x_1 + mean(frac)] + Kbar'
```
**候选恒等式**：`M = logp·[(1−sF)x_1 + mean(frac_j)] + Kbar'`；
其中 `mean(frac) ∈ [0,1)`（有界），`Kbar'` 含 tame/arch/ind2 的剩余有界项。

## 4. 抵消性分析

- `(1−sF)x_1` 随 m 线性负（sF>1，l≥5）；
- `mean(frac)` 至多 1（每 j 的 frac<1，平均后 <1）⇒ **不能抵消线性负项**；
- `Kbar'` 的 tame/arch/shellDefect 有界（VcI:313-319：`|shellDefect+orderVol| ≤ Σ(3+log e)`）；
- 故大 m 时 `M → −∞`，除非 `Kbar'` 含另一个 ∝m 正项（非 floor/frac 来源）。

## 5. 权重拆分（AM-GM/凸性）尝试

令 `w_j := j²/(nC*sF) ≥ 0`，则 `Σ_j w_j = 1`；
`A = Σ_j w_j A`；但 qScale 总和 `(1/nC)Σ_j j² A = sF A`；
配对后每项 `w_j A − (1/nC) j² A = A*w_j − A*sF*w_j = (1−sF)A*w_j < 0`（sF>1），
**权重拆分保持负号**（每项同号），AM-GM 不能改变总系数 sF>1 的事实。
（若取 w_j 使 Σw_j < sF 也无用：qScale 固定为 sF A。）

## 6. Lean 陈述草案（纯算术）

```lean
/-- j-square sum identity (ported from the green file). -/
theorem sum_jsq_eq_nC_mul_sF (nC : Nat) (sF : Real) (h : (∑ j in Finset.range nC, ((j : Real) + 1) ^ 2) = nC * sF) :
    (1 / (nC : Real)) * (∑ j in Finset.range nC, ((j : Real) + 1) ^ 2) = sF := by
  rw [h]
  field_simp

/-- Linear cancellation: (1/nC) sum j^2 x1 = sF x1. -/
theorem mean_jsq (nC : Nat) (sF x1 : Real)
    (h : (∑ j in Finset.range nC, ((j : Real) + 1) ^ 2) = nC * sF) (hn : (nC : Real) ≠ 0) :
    (1 / (nC : Real)) * (∑ j in Finset.range nC, ((j : Real) + 1) ^ 2 * x1) = sF * x1 := by
  rw [Finset.sum_mul, ← Finset.sum_mul, h]
  field_simp [hn]

/-- Algebraic decomposition with frac: M/logp = (1-sF)x1 + mean frac + Kbar/logp. -/
def MLogp (nC : Nat) (x1 : Real) (frac Kbar : Fin nC -> Real) : Real :=
  (1 - sF) * x1 + (1 / (nC : Real)) * (∑ i, frac i) + (1 / (nC : Real)) * (∑ i, Kbar i)

/-- frac terms are bounded: 0 <= mean frac < 1. -/
theorem mean_frac_bound (nC : Nat) (hn : 0 < nC) (frac : Fin nC -> Real)
    (h0 : forall i, 0 <= frac i) (h1 : forall i, frac i < 1) :
    0 <= (1 / (nC : Real)) * (∑ i, frac i) ∧
      (1 / (nC : Real)) * (∑ i, frac i) < 1 := by
  constructor
  · apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg fun i _ => h0 i
  · rw [div_mul_eq_mul_div, one_mul]
    apply div_lt_one
    · exact_mod_cast hn
    · calc (∑ i, frac i) < ∑ i, (1 : Real) := by
        exact Finset.sum_lt_sum (fun i _ => (h1 i).le) ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i _ => h1 i)
      _ = nC := by simp
```
（真实文件以 `hΣ` 替换 `sF` 定义，并接 green `sFactor`；frac 的实现需 `Int.fract` 的 `fract_nonneg`/`fract_lt_one`。）

## 7. 结论

1. 纯代数重排给出 **`M = logp·[(1−sF)x_1 + mean(frac_j)] + Kbar'`**；
2. `mean(frac)` 有界（<1），`(1−sF)x_1` 线性负 ⇒ **floor/frac 无法抵消极性**；
3. 权重拆分（`Σw_j=1`, `w_j=j²/(nC sF)`）后每项仍同号（系数 `sF>1`），AM-GM 无效；
4. 故代数层面只能接受：**需要另一个 ∝m 正项**（候选：`logShellRadius(scaled)` 的 ord 项、
   `orderVol`/`PacketIndexForm`）或显式 (UB)/`VariantBoundedQ`；
5. 与 A1018/A1022/A1030 一致；floor/frac 只解释有界振荡，不改变线性符号。