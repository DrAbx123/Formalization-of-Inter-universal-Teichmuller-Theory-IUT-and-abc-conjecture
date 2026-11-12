# NERON-TATE-ROUTE — q-pilot 线丛 = Tate 参数线丛？Faltings 高度路线 (A1103b)

| field | value |
|---|---|
| Status | ANALYSIS (no Lean; no compile) |
| 事实 | `qPilotIdeal = π₅⁺π₅⁻π₂₁₆₁⁺π₂₁₆₁⁻`（Gaussian 素数积），`absNorm = 5²·2161²`；2161 为 split multiplicative 坏约化位（S2687/S2701 链） |
| 结论 | q-pilot 更像 **Néron 模型/Tate 参数线丛**，不是模 X(5) 拉回；Faltings height/theta metric 给出 **显式 arch 公式（A，LITERATURE）**，但“目标下界化为已证高度不等式”= **C（未找到该形式）**；完整路线 = 条件性 A（需三条识别） |

## 1. q-pilot 线丛的真相

```
S2735: qPilotIdeal = gaussianFieldFivePrimePlus * gaussianFieldFivePrimeMinus
              * gaussianField2161Plus * gaussianField2161Minus
      absNorm(qPilotIdeal) = 5^2 * 2161^2
qPilotLineBundle := (qPilotIdeal : FractionalIdeal ...)
```
- 支撑 = {5, 2161}（坏约化位）；2161 是 split multiplicative 位 ⇒ 该位有**Tate 参数 q_2161**
  与 Néron 模型的分量群/特殊纤维；
- 该理想是**整性理想**（除子），在坏约化位对应 Tate 参数/特殊纤维信息，
  而非模形式 q-展开的系数——模 X(5) 拉回在坏约化位需要 Néron 模型/整模型（新增非平凡算术）。

## 2. q-pilot 是否等于 Tate 参数线丛？

```
在 split multiplicative 位 p，Tate 曲线 E_q: y²+xy = x³+a4(q)x+a6(q), q = exp(2πiτ) 型；
q-参数在 Néron 模型的特殊纤维上给出 O(1) 型线丛/除子（divisor of q-parameter）；
qPilotIdeal 的 p-进 valuation = ord_p(qPilotLineBundle) 应与 Tate 参数的 valuation 对应。
```
- **可测判据**：对每个坏位 p，`v_p(qPilotLineBundle) = ord_p(q_p)`（Tate 参数），
  且 `absNorm` 的指数（5 与 2161 各 2）与局部 valuation/分量群对所有齐；
- 我们仓库已有 `qOrder`（`tateParam.toOrdered.orderNat`，Cor312/ThetaData/Basic:171-194）
  与 `ordp_qrootOf = qOrder/(2l·e_w)`（Data:327-330）⇒ exact valuation 可算；
- **待证**：`qPilotLineBundle = ∏_p (Tate 参数除子)^{n_p}` 的精确陈述（需构造 Tate 线丛，当前仓库无）；
  ⇒ 这是 **GAP-TATE-BUNDLE**（几何对象缺失），不是已被定义的东西。

## 3. Faltings height/theta metric 的显式 arch 公式（A，LITERATURE）

经典公式（Faltings；Arakelov；Silverman/Height 书）：对椭圆曲线 `E/K`，
```
h_F(E) = (1/[K:Q]) * Σ_σ log( (1/2) ∫_{E_σ(C)} |ω|² )  型（相对对偶层 ω = det Hodge）
```
对 Tate 曲线（`q = exp(2πiτ)`）：
```
Δ = q * ∏_{n≥1}(1−q^n)^{24}  ⇒  log‖Δ‖ / 12 = log|q|/12 + Σ log|1−q^n|
⇒ Faltings height 的 arch 部分显式含 −log|q|/12 与 |η(τ)|（Kronecker 极限公式）
```
⇒ **arch 显式公式 = A（LITERATURE）**：`log|q|` 与 `h_F`、`|η|` 的关系显式。

## 4. 目标下界能否化为已证高度不等式？

目标：`−A ≤ rhs`（`A=|log q|`, `rhs=−|log Θ|`）⇔ `|log q| ≥ |log Θ|`。
用 Faltings 公式：`log|q| = 12·h_F + ...`（+η 项），`|log Θ|` 由 theta hull log-volume 给；
目标是 `|log q| ≥ |log Θ|`，即 `12 h_F + (eta terms) ≥ |log Θ|`。
**是否已有定理**：
- Faltings height 的**上下界**（如 `h_F ≥ −c log N + ...`）是 Szpiro/height 比较类结果，
  但**不是** `h_F` 与 theta-hull volume 的直接比较；
- paper 的 Cor 3.12 本身是 `|log q| ≤ |log Θ|`（方向可能相反，按 paper `−|logΘ| ≥ −|log q|` 即 `|logΘ| ≤ |log q|`）
  ——这正是我们的 target，而不是经典高度不等式的直接推论；
- 未找到一条已证高度不等式恰好给出该形式 ⇒ 判定 **C（不能化为已证定理）**；
  Faltings 公式只给**显式表达式**（A 工具），不给比较。

## 5. A/B/C 判定

| 子命题 | 类型 | 理由 |
|---|---|---|
| q-pilot = Tate 参数线丛 | **GAP-TATE-BUNDLE（需构造）** | 支撑/valuation 匹配是判据，但 Tate 线丛未构造 |
| Faltings height/eta 显式 arch 公式 | **A（LITERATURE）** | 经典公式 |
| `|log q|` 的显式 arch 表达 | **A 条件** | 用 Faltings 公式 + η |
| 目标 `|log q| ≥ |log Θ|` 由已证高度不等式推出 | **C** | 无此形式定理；Cor 3.12 即目标本身 |
| 完整路线 | **条件性 A** | 需 GAP-TATE-BUNDLE + 度量识别 + theta-hull↔height 桥 |

## 6. 需要的新构造（若走此路线）

```
(T1) Tate 曲线 E_q / Tate 参数线丛（在坏位 p=5,2161）；
(T2) 证明 qPilotLineBundle = ∏_p (Tate 参数除子)^{n_p}（valuation 对齐）；
(T3) 把 qPilot 的 arch 度量识别为 Faltings/theta 度量（ω = det Hodge 的相对度量）；
(T4) 把 theta-hull log-volume 与 Faltings height 联系（这一步等价于我们的 hcmp 几何内容）。
```

## 7. Lean 签名草案

```lean
/-- Tate parameter line bundle data at bad places (explicit data, no inhabitant). -/
structure TateBundleData where
  badPlaces : Type
  tateParam : badPlaces → Real      -- q_p
  valuation : badPlaces → Int
  valuation_matches : Prop          -- v_p(qPilotLineBundle) = ord_p(tateParam)

/-- Faltings height with the classical arch formula (LITERATURE input). -/
structure FaltingsHeightData where
  hF : Real
  logQ : Real
  etaTerm : Real
  formula : hF = logQ / 12 + etaTerm   -- placeholder, exact normalization TBD

/-- Conditional: explicit height formula + Tate identification give an expression,
but not the comparison `|log q| >= |log Theta|`. -/
theorem logQ_eq_of_faltings (F : FaltingsHeightData) :
    F.logQ = 12 * (F.hF - F.etaTerm) := by
  rw [F.formula]
  ring
```

## 8. 结论

1. qPilotIdeal 的支撑 {5,2161} 与 split multiplicative 位一致 ⇒ 更像 **Néron 模型/Tate 参数线丛**，
   而非模 X(5) 拉回（后者在坏位需 Néron 模型，新增非平凡算术）；
2. 判据：每个坏位 `v_p(qPilotLineBundle) = ord_p(q_p)`，且 absNorm 指数匹配（5²·2161²）；
3. Faltings height/theta metric 的 arch 公式是**显式经典公式（A）**，给出 `log|q|` 的表达式；
4. 但把目标化为“已证高度不等式”= **C**：未找到该形式定理；Cor 3.12 就是目标本身；
5. 完整路线 = 条件性 A，需 (T1)-(T4)；当前仓库无 Tate 线丛构造（GAP-TATE-BUNDLE）。
6. 与 A1098/A1097 一致：q-pilot 无现成模解释；Néron/Tate 方向是更贴近其算术本质的描述。