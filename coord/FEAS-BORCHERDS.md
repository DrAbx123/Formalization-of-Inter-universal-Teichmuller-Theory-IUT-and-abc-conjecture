# FEAS-BORCHERDS — Borcherds 乘积作截面 s 的可行性 + θ 归一化数值

日期：2026-11-13；qpilot（A1099，承 A1096/A1097）。**Sage/Python + 文献检索**；未跑 Lean。

## 1. Borcherds singular theta lift：已知结构

标准定理（Borcherds 1998；Bruinier 2002 等）：
给定偶 lattice L（signature (2,n)）与弱全纯向量值模形式 F（dual Weil rep，权 1−n/2，principal part 整系数），
得到 Grassmannian `O(L)/(O(2)×O(n))` 上的亚纯自守形式 Ψ(F)，且：
```
weight(Ψ) = c(0)/2
div(Ψ) = Σ_{λ∈L, λ²>0} c(−λ²/2) Z(λ)   （Heegner 除子）
Ψ 有显式无穷乘积（Borcherds product formula）
```
来源：R. Borcherds, *Automorphic forms with singularities on Grassmannians*, Invent. Math. 132 (1998)；J. Bruinier, *Borcherds products on O(2,l) and Chern classes of Heegner divisors* (2002)。

**能直接给的东西**：除子（Heegner 除子）显式、权显式、q-展开/产品公式显式。
**不能直接给的东西**：
- 没有给“canonical 归一化截面的 sup 范数 ≤1”的定理；arch 范数依赖所选 Hermitian metric/归一化；
- 有限的 p 进整除性/生成性需要 q-展开整系数/首系数可逆，不是 Borcherds 定理自动给；
- Borcherds 形式活在正交 Shimura 簇上，不是我们的 DetBundle/算术曲线上的截面。

## 2. 与我们的截面 s 的适用性

我们的 `s` 是 FEAS-DELIGNE/OUTSIDE-DELIGNE 中的 **DetBundle 截面**（Arakelov 度、有限位生成性、arch 范数界）。Borcherds 乘积作为 s 需要：

1. **空间映射**：我们的 base（算术曲线/DetBundle）到某个 `O(2,n)` Shimura 簇的嵌入，且线丛与 Borcherds 权线丛一致；**当前没有**；
2. **除子匹配**：Borcherds 除子是 Heegner 除子，而我们的有限位整除/坏位除子不是 Heegner 型；**一般不能控制任意 bad prime**；
3. **arch 范数**：需要把 Borcherds 形式在所选 metric 下的 sup 范数压到 ≤1（或所需符号），Borcherds 定理无此结论；
4. **整性/生成性**：需要 q-展开整系数 + 有限位首系数 unit；Borcherds 输入整 principal part 不自动保证目标整性。

### 2.1 在 X0(N) 上的可能限制
Borcherds products on X0(N)（signature (2,1) lattice）存在，并有 converse theorem 刻画哪些 Heegner 除子来自 Borcherds 乘积（Nagoya Math. J., *A converse theorem for Borcherds products on X0(N)*）。
即使取 X0(N)：
- 只有特定 N、特定 Heegner 除子/权；不是任意曲线/任意 bad prime；
- 我们的 11a1/37a1/14a1 等 q-pilot 曲线没有给出对应的 lattice/输入形式；
- 有限位整除仍不匹配。

## 3. A/B/C 判定

| 子目标 | 判定 | 理由 |
|---|---|---|
| 用 Borcherds product 直接作我们的 s（general DetBundle/曲线） | **C** | 空间/线丛无映射；除子非 Heegner；无 arch sup 界 |
| 限制到 X0(N) 且 divisor 匹配 Heegner + 显式 arch 估计 | **B（条件）** | 有 Borcherds/converse 理论，但需构造 lattice/输入 F + arch 小范数 + 整性；当前无 |
| 只借 Borcherds 除子/权/乘积公式做簿记 | **C/B** | 可作工具，不推出 hcmp/N5；需额外桥 |

**总判定：C（直接作 s 不可行）；B 仅在强限制的 X0(N)+Heegner+arch 估计下有条件可能。**

## 4. θ 归一化数值（A1099 第二部分）

Sage 周期 τ：11a1, 37a1, 14a1；θ[α,β](z;τ)=Σ_n exp(πi(n+α)²τ+2πi(n+α)(z+β))，α,β∈{0,1/2}。

### 4.1 θ 变换关系
- **T**: `θ[α,β](z+1;τ) = e^{2πiα} θ[α,β](z;τ)`；数值比值 = **1.000000**（三曲线四 char）；
- **S**: 手算候选 `θ[α,β](z/τ;−1/τ) = e^{πiz²/τ}θ[β,−α](z;τ)` 的比值不是 1，而是一个**固定相位/常数**（11a1 约 1.096−0.228i；37a1 约 1.105；14a1 约 0.990−0.143i；随 τ/char 变）。
⇒ 需要标准 theta multiplier/characteristic 归一化；当前公式缺一个显式常数因子。

### 4.2 归一化乘积 sup 范数
`P_J(z)=∏_{j=1..J}|θ[α,β](j z)/θ[α,β](0)|^{j²}`；对全部 24 个非零 5-torsion lift 取 max log P_J。

| curve | char | maxlog J=1 | J=2 | J=3 | J=4 | pass≤1 lifts J=4 |
|---|---:|---:|---:|---:|---:|---:|
| 11a1 | [0,0] | 2.264 | 38.43 | 223.86 | 814.19 | 4/24 |
| 11a1 | [0.5,0] | 2.376 | 40.11 | 229.00 | 821.65 | 4/24 |
| 37a1 | [0,0] | 2.359 | 40.55 | 236.95 | 863.95 | 4/24 |
| 14a1 | [0,0] | 1.885 | 32.29 | 187.48 | 680.43 | 4/24 |
| 11a1 | [0.5,0.5] | 39.60 | 226.09 | 749.95 | 1937.35 | 0/24 |
| 37a1 | [0.5,0.5] | 39.80 | 229.00 | 765.67 | 1991.20 | 0/24 |

- 对全部 24 个 lift，**没有 characteristic 使 max P_J≤1**（J=4 最好也只有 4/24 lifts 通过）；
- 固定 primitive 基 `u0=(1+0τ)/5` 且 char [0,0]/[0.5,0] 时 product≤1（A1092），但 sup over lifts 远大于1；
- maxlog 随 J 增长：J1→J4 约 ×300（11a1 [0,0]:2.26→814），远快于 `Σj²` 的比例5；**没有简单的 j² 权重线性关系**，取决于 θ 在某个 torsion lift 上接近零。

## 5. 结论

1. **Borcherds 直接作 s：C**。空间/线丛/除子/arch 四处不匹配；X0(N)+Heegner+arch 限制下最多 **B**；
2. Borcherds 乘积提供显式除子和权，但不提供 canonical arch sup≤1，也不控制一般 bad-prime 整除；
3. θ 归一化数值：T 变换精确；S 变换缺常数；全 torsion 的归一化 P_J sup 远大于1，只有特定 u0/char 的 product≤1；
4. maxlog 随 J 超 `Σj²` 增长，不存在简单 j 权重 sup 界；要 arch 小范数需更精细的 theta group/截断证明。

## 文件
- `coord/theta_normalization.csv`（3 curves × 4 chars：T/S ratio、maxlog J=1..4、pass counts）
- 本文件 `coord/FEAS-BORCHERDS.md`

## 文献
- R. Borcherds, *Automorphic forms with singularities on Grassmannians*, Invent. Math. 132 (1998).
- J. Bruinier, *Borcherds products on O(2,l) and Chern classes of Heegner divisors*, Lecture Notes in Math. 1780 (2002).
- *A converse theorem for Borcherds products on X0(N)*, Nagoya Math. J. (检索确认标题/摘要；正文未逐句核).