# THETA-ARCH-NUMERIC — θ(u_j) 乘积的数值检验

日期：2026-11-13；qpilot（A1088）。**Sage + Python**；未跑 Lean。

## 1. 样本与归一化

曲线（Cremona label）和 Sage 周期格：

| curve | conductor | τ = ω2/ω1 |
|---|---:|---|
| 11a1 | 11 | 0.500000 + 1.149390i |
| 37a1 | 37 | 0.000000 + 1.221127i |
| 14a1 | 14 | 0.283198 + 0.959061i |
| 21a1 | 21 | 0.000000 + 1.059036i |
| 38a1 | 38 | −0.423872 + 0.905722i |

Sage 取 `E.period_lattice().basis()`, `τ=ω2/ω1`（Im τ>0）。ℓ=5；torsion 坐标取 `z=(a+bτ)/5`，`(a,b)≠(0,0)`（共24个 lift）。

标准 theta（无特征）：
```
θ(z;τ) = Σ_{n∈Z} exp(πi n²τ + 2πi n z)
product_j = ∏_j |θ(j z;τ)|^{j²},  j=1..J
Normalized: |θ(jz;τ)/θ(0;τ)|^{j²}
```
数值：Python `cmath`，n=−100..100；Sage 只负责周期格/τ。

## 2. 结果（每个 curve，24 个 lift）

### J=1..2（nC=2）

| curve | raw min | raw max | raw ≤1 的 lift 数 | norm min | norm max | norm ≤1 数 |
|---|---:|---:|---:|---:|---:|---:|
| 11a1 | 0.092603 | 4.91e16 | 2/24 | 0.091929 | 4.88e16 | 6/24 |
| 37a1 | 0.222145 | 5.02e17 | 4/24 | 0.179849 | 4.07e17 | 6/24 |
| 14a1 | 0.098967 | 1.44e14 | 4/24 | 0.072363 | 1.06e14 | 6/24 |
| 21a1 | 0.193719 | 3.32e15 | 4/24 | 0.136963 | 2.35e15 | 6/24 |
| 38a1 | 0.067499 | 2.61e13 | 4/24 | 0.057183 | 2.21e13 | 6/24 |

### J=1..4

| curve | raw min | raw max | raw ≤1 的 lift 数 | norm min | norm max | norm ≤1 数 |
|---|---:|---:|---:|---:|---:|---:|
| 11a1 | 1.014889 | ∞ | 0/24 | 0.971401 | ∞ | 4/24 |
| 37a1 | 0.649316 | ∞ | 4/24 | 0.182845 | ∞ | 4/24 |
| 14a1 | 0.555696 | 2.10e296 | 4/24 | 0.084920 | 3.21e295 | 4/24 |
| 21a1 | 0.480933 | ∞ | 4/24 | 0.060071 | ∞ | 4/24 |
| 38a1 | 0.825969 | 8.61e279 | 4/24 | 0.305335 | 3.18e279 | 4/24 |

（“∞”是 θ 在某 torsion lift 上非常接近零点导致的数值发散；min/max 为24个 lift 的极值。）

## 3. 判读

- **没有观察到“所有 lift 都 ≤1”**：J=1..4 的 raw 在5条曲线上最多 4/24 lifts ≤1；J=1..2 有 lift 通过但最大到 1e17；
- 归一化 θ/θ(0) 不解决问题（max 仍在 1e13–1e295）；
- 关键原因：**标准 θ 不是 E(C) 上的函数**，它只对 lift `z` 有定义且满足 quasi-periodicity；`z=(a+bτ)/5` 的不同 lift 给出不同值，乘积不是 torsion 点的规范量。arch 小范数假设需要一个**固定的 theta 特征/归一化**（characteristic、theta quotient、或 IUT 的特定 theta 值），当前数据没有该规范；
- 因此这组数值**不支持**“标准 θ 的原始乘积 ≤1”作为普遍 arch 小范数；若要检验 IUT 假设，必须给出 θ 的 characteristic/归一化及 `u_j` 的具体选取。

## 4. 需要的归一化说明

1. **theta 特征/characteristic**（如 θ[a,b]）或 theta quotient，使值在 lattice 变换下按已知因子变换；
2. **u_j 的选取**：是某个 primitive ℓ-torsion 的 j 倍，还是全部 torsion 点的排序；不同选择结果差异巨大；
3. **周期/ℓ 归一化**：ω1 的取值（real period）不影响 τ/theta 形状，但若 θ 的宗量用 ω1 归一化，需固定；
4. 乘积的指数 j² 与 j 范围（nC=2 还是 ℓ−1=4）需与 paper 定义一致。

## 5. 结论

Sage 周期矩阵/τ 与 5-torsion 已可算；但标准 θ 的原始乘积不普遍 ≤1，且非规范。当前只能给出“某些 lift 通过、某些发散”的数值旁证，不能确认 arch 小范数假设；需补充 theta characteristic/归一化后才能做决定性数值检验。

## 文件
- `coord/theta_arch_numeric.csv`（5 curves × J=1..2/1..4：min/max/≤1 counts）
- `tmp/theta_curves.sage`（Sage 周期/τ）
- `tmp/theta_num2.py`（theta 乘积）
- 本文件 `coord/THETA-ARCH-NUMERIC.md`