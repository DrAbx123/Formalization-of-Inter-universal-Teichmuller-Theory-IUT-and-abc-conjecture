# NERON-TATE-FEASIBLE — q-pilot 主理想 + Faltings/theta 度量的显式化方案 (A1104)

| field | value |
|---|---|
| Status | PLAN (explicitization scheme; no Lean, no compile) |
| 关键事实 | `qPilotIdeal = π₅⁺π₅⁻π₂₁₆₁⁺π₂₁₆₁⁻ = (5)·(2161) = (10805)` —— **主理想** ⇒ q-pilot 线丛在 `Pic(K)` 中**平凡**；内容全在**度量/整模型**（Néron/Tate 参数、Faltings height/theta metric） |
| 判定 | 显式化机器 = **A（经典）**；目标化为显式不等式 = **A 条件**（需度量识别 + 解析不等式）；非拓扑障碍 |

## 0. 主理想事实与其含义

```
qPilotIdeal = gaussianFieldFivePrimePlus * gaussianFieldFivePrimeMinus
              * gaussianField2161Plus * gaussianField2161Minus
            = (5) * (2161) = (10805)        （Gaussian 整数中 5, 2161 均分裂，ππ̄ = p）
⇒ qPilotLineBundle ≅ O_K（Pic 中平凡）
```
- 因此**不存在**由理想类给出的拓扑/除子障碍；
- q-pilot 的全部内容 = **主化截面 + 其 arch/p-进度量 + 整模型（Tate 参数）**；
- 这与 paper Step (xi-d) 的 “localizations + determinant + normalized log-volume” 结构一致：
  度量的归一化就是全部内容。

## 1. concrete S1487 的完全显式化方案

### 1.1 A = logQ/(2ℓ)

```
logQ = Σ_{w | bad} weight_w * qOrder_w * log p_w
     = weight_5 * qOrder_5 * log 5 + weight_2161 * qOrder_2161 * log 2161
A    = logQ / (2l)
```
- `weight_w`：place weight（`Q.weight` 归一化；split multiplicative 位的权重由局部数据给）；
- `qOrder_w`：Tate 参数阶，`qOrder_w = ((tateParamAt ...).toOrdered unifAt).orderNat`（Cor312/ThetaData/Basic:171-194）；
  - 具体曲线例：`11a1 → I5` 时 qOrder=5，`858k2 → I21` 时 21，`9546f3 → I72` 时 72（**NUMERIC 样本**）；
  - S1487 具体 Gaussian 数据：需读 `S1487Cand` 的 Tate 参数/约化型（GAP: S1487 的 qOrder 需从具体数据提取）；
- 5 与 2161 均 split multiplicative（lead 事实）⇒ qOrder = 分量的阶，可用 `ordp_qrootOf = qOrder/(2l·e_w)`（Data:327-330）核对。

### 1.2 R = theta hull log-volume

```
R = |log Θ| = -S2717ThetaHullLogVolume          （S2717:50-67，signed）
  = haarLogVolume μ (actualC3LogShellTensorRegion C3)   （S2807:40-47）
  = Σ_{arch σ} log( Haar_σ(θ-hull region) )     （per embedding）
```
其中 `μ = actualC3LogShellTensorHaar C3`（A1088/A1059 的 C3 Haar）。
**具体化**：θ-hull 的 region 是 `tensorIntegralRegion` 的 `leastHull` 型区域（Ind3:57-62、C3LogShellTensorLActual）；
其 arch 体积由 log-shell 半径与 `q^{j²}` 缩放（`scaleElt`）决定。

### 1.3 CTheta

```
CTheta = (l+1)/4 * |log q| * { (1 + 12 d_mod/l)(log d_Ftpd + log f_Ftpd)
                              + 10(e*_mod*l + η_prm) - 1/6(1 - 12/l^2) log q } - 1    (S2691:111-116)
```
`|log q| = Σ_p weight_p qOrder_p log p`（= 2ℓ·A）；`d_mod, d_F, f_F, e*, η` 由 S1487 数据的具体算术参数给。

## 2. Faltings height / theta metric 的显式化

### 2.1 经典公式（LITERATURE）

```
对 E/K（K = Q(i), [K:Q]=2）：
h_F(E) = (1/[K:Q]) * Σ_σ log( (1/2) ∫_{E_σ(C)} |ω|² )     （Faltings/Arakelov；ω = 对偶层）
Tate 曲线（q = exp(2πiτ)）：
  Δ(q) = q * ∏_{n≥1}(1−q^n)^24
  ⇒ log|Δ| / 12 = log|q|/12 + Σ_n log|1−q^n|
⇒  log|q| = 12*( h_F + (1/[K:Q])Σ_σ log η_σ + 常数 )       （Kronecker 极限公式）
```
这是**显式经典机器（A）**：把 `log|q|` 表达为 `h_F` + eta 项 + 常数。

### 2.2 目标的显式不等式

```
目标: -A <= -R  ⇔  A >= R  ⇔  logQ/(2l) >= |log Θ|
用 logQ = Σ_p w_p qOrder_p log p（p ∈ {5,2161}）：
  A = [w_5 qOrder_5 log5 + w_2161 qOrder_2161 log2161] / (2l)
R  = haarLog(θ-hull)  （§1.2 的显式 Haar 体积）
⇒ 显式不等式:
  w_5 qOrder_5 log5 + w_2161 qOrder_2161 log2161  >=  2l * |log Θ|   … (INEQ)
```
其中 `|log Θ|` 用 Faltings/theta metric 展开（§2.1）后，`INEQ` 变为
关于 `h_F(E)`、`q_5, q_2161`、`η_σ`、`ℓ` 的**显式不等式**。

### 2.3 判断：这是否把目标化为已证定理？

- 显式化本身 = **A（经典公式）**；
- 但不等式 `(INEQ)` 的**证明**仍需：
  (i) q-pilot 的度量 ≡ Faltings/theta metric（GAP-METRIC）；
  (ii) θ-hull 体积的 arch 展开与 eta/theta 值一致（GAP-HULL-METRIC）；
  (iii) 对 `h_F` 与 `qOrder` 的**解析估计**（本题的核心不等式）；
- 目前 (i)-(iii) 均未证 ⇒ 整体 = **A 条件**（显式化 A；比较 C/B）。

## 3. 一般化（任意 ABC 三元组）需要什么

```
(G1) 每个坏位 p 的局部型：split multiplicative / non-split multiplicative / additive，
     conductor 指数 f_p、Néron 分量群 Φ_p；
(G2) 每个 split multiplicative 位的 Tate 参数 q_p 与 qOrder_p；
(G3) 全部 arch 嵌入 σ : K → C 的 Faltings 度量与 η/θ 值；
(G4) 一般 K（[K:Q]>2）的 Faltings height 归一化（1/[K:Q] 与 ω 的选取）；
(G5) qPilotIdeal 的一般支撑（坏位集合）与其主化截面；
(G6) θ-hull 区域的 arch 体积对一般 K 的显式化；
(G7) 最终解析不等式对 (q_p, η_σ, h_F) 的统一估计。
```
对任意 ABC 三元组，还需要把 (G1)-(G7) 从 elliptic curve/ABC 数据构造出来；当前仓库只有部分
（`qOrder`、`ordp_qrootOf`、Faltings 相关标量），没有完整 Tate/Néron 模型形式化。

## 4. Lean 签名草案

```lean
/-- Concrete S1487 explicit data. -/
structure S1487ExplicitData where
  l : Nat
  w5 : Real
  w2161 : Real
  qOrder5 : Nat
  qOrder2161 : Nat
  logQ : Real
  A : Real
  A_eq : A = logQ / (2 * (l : Real))
  logQ_eq : logQ = w5 * (qOrder5 : Real) * Real.log 5 + w2161 * (qOrder2161 : Real) * Real.log 2161
  R : Real            -- |log Theta|
  CTheta : Real

/-- Faltings height / theta metric explicit arch formula (LITERATURE input). -/
structure FaltingsArchData where
  hF : Real
  logQ : Real
  etaTerm : Real
  constTerm : Real
  formula : logQ = 12 * (hF + etaTerm + constTerm)

/-- Target as an explicit inequality, given the Faltings formula. -/
theorem target_of_explicit_ineq (D : S1487ExplicitData) (h : D.R ≤ D.A) :
    -D.A ≤ -D.R := by
  linarith
```

## 5. 结论

1. **qPilotIdeal = (10805) 主理想** ⇒ Pic 中平凡，内容全在度量/整模型（Néron/Tate）；
2. S1487 显式化：`A = [w_5 qOrder_5 log5 + w_2161 qOrder_2161 log2161]/(2ℓ)`，`R = haarLog(θ-hull)`，
   `CTheta` 由 S2691 公式代入；
3. Faltings/theta metric 给 `log|q| = 12(h_F + η项 + 常数)`（**A 经典公式**），
   目标化为显式不等式 `w_5 qOrder_5 log5 + w_2161 qOrder_2161 log2161 ≥ 2ℓ·|log Θ|`；
4. 判定：显式化 = A；比较本身仍需 (i)-(iii) 三条识别/估计（GAP-METRIC/HULL-METRIC/解析不等式）
   ⇒ **A 条件**，不是已证；
5. 一般化 (G1)-(G7) 是任意 ABC 三元组所需；当前仓库缺 Tate/Néron 模型完整形式化。
6. 下一步（若继续）：先做 (i) 度量识别（q-pilot ↔ Faltings/theta metric），再攻 (iii) 的解析估计；
   这比模曲线/Klein 路线更贴近 qPilotIdeal 的算术本质。