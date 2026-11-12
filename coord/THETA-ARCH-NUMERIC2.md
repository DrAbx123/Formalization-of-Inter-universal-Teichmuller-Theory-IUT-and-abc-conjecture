# THETA-ARCH-NUMERIC2 — characteristic 归一化后的 θ 乘积

日期：2026-11-13；qpilot（A1092）。**Sage 周期/τ + Python 手算 Riemann theta with characteristic**；未跑 Lean。

## 1. 归一化

```
θ[α,β](z;τ) = Σ_{n∈Z} exp(πi(n+α)²τ + 2πi(n+α)(z+β)),   α,β ∈ {0,1/2}
quotient: θ[α,β](z;τ)/θ[α,β](0;τ)
product_j = ∏_{j=1..J} |θ[α,β](j u0;τ)/θ[α,β](0;τ)|^{j²}
```
样本：11a1, 37a1, 14a1（Sage period lattice 得到 τ）。

## 2. u_j 的两种选取

1. **multiples**：固定 primitive 5-torsion 基 `u0=(1+0·τ)/5`，`u_j=j u0`（j=1..4 或 1..2）；
2. **all_torsion**：遍历全部 24 个非零 5-torsion lift `u=(a+bτ)/5`，取各 lift 的 product 的**最大值**（最坏情况）。

## 3. 结果（log product；≤0 即 max modulus ≤1）

### 3.1 multiples u0=(1+0τ)/5, J=1..4

| curve | char [0,0] | char [0.5,0] | char [0,0.5] | char [0.5,0.5] |
|---|---:|---:|---:|---:|
| 11a1 | **−0.0290** ✅ | **−18.818** ✅ | −0.0290 ✅ | +1106.3 ❌ |
| 37a1 | **−1.5040** ✅ | **−18.902** ✅ | +1.5410 ❌ | +1108.1 ❌ |
| 14a1 | **−2.1921** ✅ | **−18.834** ✅ | +2.1522 ❌ | +1109.6 ❌ |

### 3.2 multiples, J=1..2

| curve | [0,0] | [0.5,0] | [0,0.5] | [0.5,0.5] |
|---|---:|---:|---:|---:|
| 11a1 | **−0.00334** ✅ | **−4.8978** ✅ | −0.00334 ✅ | +185.26 ❌ |
| 37a1 | **−0.34009** ✅ | **−4.9168** ✅ | +0.34435 ❌ | +185.57 ❌ |
| 14a1 | **−0.49090** ✅ | **−4.9014** ✅ | +0.48628 ❌ | +185.82 ❌ |

### 3.3 all_torsion（24 lifts 的最大 log product）

| curve | J=1..4 max | J=1..2 max |
|---|---:|---:|
| 11a1 | 814.2 … 1937.3（各 char） | 38.4 … 226.1 |
| 37a1 | 863.8 … 1991.2 | 40.5 … 229.0 |
| 14a1 | 680.4 … 1802.2 | 32.3 … 219.6 |
⇒ **对全部 24 个 lift，没有 characteristic 使 max product ≤1**。

## 4. 判读

- **归一化 quotient 确实能给出 ≤1**：固定 primitive 基 `u0=(1+0τ)/5`，取 characteristic **[0,0] 或 [1/2,0]**，J=1..2 和 J=1..4 的 product 在 3 条曲线上均 ≤1；
- **不是所有 characteristic**：`[0,1/2]` 对 37a1/14a1 变正；`[1/2,1/2]` 全部巨大（~e^1100）；
- **不是所有 lift**：all-torsion 最大值仍 e^32–e^1991；θ 的 quasi-periodicity/lift 依赖依然存在；
- 因此 arch 小范数只能对一个**固定的 theta group/canonical section + 固定 u0** 成立；`u0=(1+0τ)/5` 与 [0,0]/[1/2,0] 是本次数值可行的候选，但需与 paper 的 theta 定义对齐。

## 5. 结论

1. theta quotient/characteristic 归一化后，存在明确选择（`u_j=j·(1/5)`, char [0,0] 或 [1/2,0]）使 3 条曲线的 product ≤1；
2. 该结论**依赖 u0 lift 与 characteristic**；全 torsion/全 characteristic 不成立；
3. 需要 paper 侧的 canonical theta group/section 来钉死选择，才能把数值旁证升级为假设验证。

## 文件
- `coord/theta_arch_numeric2.csv`（3 curves × 4 chars × modes，log product/pass）
- `tmp/theta_char2.py`（手算 Riemann theta 脚本）
- 本文件 `coord/THETA-ARCH-NUMERIC2.md`