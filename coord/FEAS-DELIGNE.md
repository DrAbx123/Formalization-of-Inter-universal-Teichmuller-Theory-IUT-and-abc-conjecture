# FEAS-DELIGNE — Deligne 小截面路线的 A/B/C 可行性判定 (A1093)

| field | value |
|---|---|
| Status | ANALYSIS (no Lean; external claims limited to confirmed references; no compile) |
| 判定框架 | **A**=可证归约（外部定理把下界化为另一已证定理/标准估计，有具体映射）；**B**=重述（同强度，无增益）；**C**=不蕴含目标 |
| 结论 | **Deligne 小截面路线 = B（deg≤0 ⇔ 小范数截面的 inf 刻画）+ 两个独立输入（arch 新估计、有限位算术）。当前**不是 A**；若 arch 显式估计 + 有限位整性被形式化，则升为 A |

## 1. 「deg≤0 ⇔ 存在小范数截面」的性质：**B（重述）**

Arakelov 度的标准 inf 刻画：
```
deg^(L) = inf over nonzero rational sections s of (1/[K:Q]) * ( Σ_arch log‖s‖_v - Σ_fin log#(L_p/O_p s) )
（符号约定按 A1087 §1；不同文献符号相反，本质相同）
```
因此：
```
deg^(L) ≤ 0  ⇔  存在非零截面 s 使 (Σ_arch log‖s‖ − Σ_fin log#) ≤ 0
```
这**就是** `deg≤0` 的重新表述（inf 的定义展开），本身**没有降低强度**。
⇒ 作为独立命题它是 **B**；要成为 A，必须把右侧的“存在截面 + 范数界/整性”
替换为一个**已被证明的标准估计定理**（arch）和**算术可证**（有限位），并把它们显式映射到我们的量。

## 2. 外部文献检索结果（有限、务实）

已确认：
- **arXiv:1106.0255 "Deligne pairing and determinant bundle"**（检索确认标题）：Deligne pairing/det bundle 的结构、度量、邻接公式；
- theta 函数的**变换公式/Fourier 展开**（标准：`θ(z+πτ)=(-qe^{2iz})^{-1}θ(z)`，`θ(z,τ)=Σ_n q^{n²/2}e^{2πinz}`）；
- Jorgenson–Kramer 型**一致 sup-norm 界**（cusp forms/automorphic forms 的平均或一致界；
  典型结果形如 `sup |f| ≤ C·(k·[SL_2(Z):Γ])^{...}·...`，针对 Hecke 本征形式/整体截面，不是
  “任意 torsion 点上的 theta 值乘积”）；
- Fay 的 theta 恒等式（τ 函数/trisecant；**显式常数与良范数**不是现成可直接引用的形式）。

**未找到**：一条现成定理，其陈述直接给出我们的 `∏_j |θ(u_j)|^{j²} ≤ 1`（或 ≤ 显式常数），
对一般 torsion 点 `u_j`、任意模曲线/椭圆曲线、并带显式 arch 常数与 p 进整性。
⇒ **arch 估计需要新证明**（或至少需要把标准 Fourier/Petersson 估计**重新推导并形式化**到我们的具体截面）。

## 3. 有限位整性：算术可证（A 型，但未在仓内）

- theta 的 q 展开 `Σ q^{n²/2}` 在 good 位给出 p 进整性（q 有正 valuation）；
- torsion 点的分母由 `l`-幂控制，`θ(u_j)` 的 p 进 valuation 可由 `ordp_qrootOf`/tame 展开计算；
- 我们的 `S3050Unit_eq_log_norm_div`（= -log‖x‖/(2l)）、`S3016`/`S3029` 提供 Step V 标量，
  但**没有** `θ(u_j)` 的 p 进 valuation 形式化。
⇒ 类型：**A-候选（算术可证）**，当前状态 = 未形式化（GAP-PVAL-THETA）。

## 4. 判定

| 子命题 | 类型 | 理由 |
|---|---|---|
| `deg≤0 ⇔ 小范数截面存在` | **B（重述）** | inf 定义的展开，无强度降低 |
| arch 上界 `∏|θ(u_j)|^{j²} ≤ 1` | **需新解析输入** | 未找到现成定理给出该具体乘积的显式界；
|  |  | Fourier/Petersson/Fay 是**工具**，不是现成结论 |
| 有限位整性/生成性 | **A-候选** | 算术可证（q 展开、ordp_qrootOf），但未形式化 |
| 合成（B + arch + finite） | **A 仅当 arch 被显式证明/引用** | 当前 = “B + 两个独立输入” |

**Deligne 路线最终判定：B（当前）；若 arch 显式估计与有限位整性形式化 ⇒ A；**
**若 arch 估计无法显式化 ⇒ 降为“需新解析输入”，不能声称 A。**

## 5. 要升为 A 需要的具体工作（可执行）

1. **arch 显式估计**：从 theta 的 Fourier 展开推导
   `log|θ(z,τ)| ≤ π·Im τ/4 + log(2) + ...`（在基本域上），再对 torsion 点 `u_j` 的具体 `Im τ` 与
   位置控制 `Σ_j j² log|θ(u_j)|`；需要显式常数与 j-average 的统一界；
2. **有限位整性**：q 展开 + `ordp_qrootOf`/tame 给出 `v_p(θ(u_j)) ≥ 0`；
3. **合成**：把 1、2 代入 `ThetaSectionData.arch_le`/`finite_ge`（我们的 A1088 模板），
   即得 `hcmp_of_theta_section : degree ≤ 0`（真证）。

## 6. Lean/接口现状

- `Mzk1ThetaSectionActual`（A1088）就是 **B-结构**：`arch_le`/`finite_ge` 是输入字段；
- 若 1、2 形式化，填充这两个字段即闭合（模板的真证部分是 `hcmp_of_theta_section`）；
- 当前**不能**把该文件当作 hcmp 的证明：它只是归约（header 已标 GAP-ARCH-THETA/GAP-PVAL-THETA）。

## 7. 结论

1. 「deg≤0 ⇔ 小范数截面」= **重述（B）**，不是增益；
2. Deligne pairing 是**工具**（给出 det bundle/度量/邻接公式），不自动给下界；
3. arch 估计**没有找到**现成定理覆盖我们的具体 theta 乘积 ⇒ 必须新证（或重新推导标准估计并形式化）；
4. 有限位整性是算术可证（A-候选），但未形式化；
5. 因此 Deligne 路线当前 = **B + 新解析输入**；只有完成 §5 的 1、2 才升为 A。