# QORDER-SIGN — qOrder 数值、无界性与 qScale 符号 (A1017)

| field | value |
|---|---|
| Status | PARTIAL (qOrder=n 钉死；无界性确认；qScale 符号按源读出为负，但与 variant 可成立性冲突 ⇒ GAP-SIGN 仍需 (Ind1)-min 口径核对) |
| 源 | AdmissiblePrime:52/152 (`qOrder`/`q_order_coprime`), IdentifiedCopies:67 (`componentVol_units_smul`), ScaleVolume:20 (`kappa(p)=-logp`), Gap:747-756 (`ind2Term`), Gap:909-935 (`proj_hull_thetaPilot`, `gapHullAt_eq`) |
| 结论 | `qOrder = n`（I_n），整数，可任意大；admissible 仅要求 `l` 不整除 n；qScale 按源符号为**负** ⇒ per-capsule 对 j>=2 在 n→∞ 时失效（除非 Ind1-min 降低系数） |

## 1. qOrder 的精确定义与数值

- `AdmissiblePrime.lean:52`: "its normalized integer order is `Iut.qOrderAt` (`Iut.InitialThetaData.qOrder`),
  independent of the uniformizer of `F_w` used to normalize it" —— qOrder 是 Tate 参数 `t` 的
  **归一化整数阶**（整数，uniformizer 无关；底层 `orderNat`，`orderNat_eq_qOrderAt`）。
- 半稳定 `I_n` 曲线：`v_p(Delta_min) = n`，Tate 参数 `q_Tate` 满足 `v_p(q_Tate) = n`
  （乘法退化 `v(j) = -n`，`j = 1/q + ...`）；故 **`qOrder = n`**（整数）。
- 不是 `n/(2l)`（会非整数，与"整数阶"矛盾），不是 `n*2l`。`q_v` 是 q_Tate 的 2l-th root
  （ThetaRegion:34-36），它的阶 `v(q_v) = n/e = n*g/(2l)`（见 E-V-DEPENDENCE），
  **但 A 侧用的 qOrder 是 Tate 参数本身的 n**，不是 q_v 的阶。

数值：
| curve | I_n | p | qOrder = n | admissible l (>=5, l not | n) |
|---|---|---|---|---|
| 11a1 | I5 | 11 | **5** | 7, 11, 13, ... (l=5 被 n 整除，排除) |
| 858k2 | I21 | 13 | **21** | 5, 11, 13 (l=7 被排除) |
| 9546f3 | I72 | ? | **72** | 5, 7, 11, 13 (l 不整除 72) |

## 2. 无界性与 admissible 的限制

- `I_n` 的 n 可任意大（半稳定 e=1，`v_p(Delta) = n` 任意）⇒ **qOrder 无界**；
- admissible 定义 3.1(c) `q_order_coprime` 只要求 `l` 与 `qOrder` 互素（`PrimeToOrder l`），
  对每个 n 都有无穷多 admissible l（取 l > n 且 l 素数即可）；
- 因此 **UB（一致 v_p 界）是真实缺口**，不能从定义 3.1 推出。

## 3. qScale 在 B_i 中的符号（源级）

1. `ind2Term`（Gap:747-754）:= `V(leastHull(thetaComponent)) − V(scaleElt • leastHull(shell))`，
   `ind2Term_nonneg`（:756-769）；`gapTerm_finite = shellDefect + ind2Term`（:780-783）。
2. `componentVol_units_smul`（IdentifiedCopies:67-72）: `mu(a • X) = mu(a • O) + mu(X)`；
   `kappa(p) = -log p`（ScaleVolume:20，`componentVol_prime_preimage'`）⇒ 对收缩单位 `a`
   （`|a| < 1`，`ord(a) > 0`）：`mu(a • O) = -ord(a)*log p < 0`. 故
   `V(scaleElt • shell) = V(shell) - ord(scaleElt)*log p`（`ord(scaleElt) = j^2 * v(q_v)`）。
3. `proj_hull_thetaPilot`（Gap:909-914）：hull(thetaPilot) 的 component =
   `leastHull(thetaComponent)`；`thetaComponent` 由 scaled shells 经 Ind2 单位扩张得到，
   故 `V(thetaHull) = V(scaleElt • shell) + ind2Term`（同 leading 的 qScale + 非负 ind2）。
4. `rhs = processionVol(thetaHull)`（RightHandSide:107）⇒ leading：
   `rhs_lead = -(1/nC) sum_i j_i^2 * v(q_v) * log p`；由 `sum_i j_i^2 = nC*sF`，
   `rhs_lead = -sF * (v(q_Tate)*log p/(2l)) = -sF * A_lead`（单 place）。
   因此 `R = -rhs = +sF * A + (positive?)`，`M = A - R` leading `= (1 - sF)*A < 0`（l>=5）。

**矛盾提示**：若按上述逐项符号，variant 对 I_n（n 大）会失败（除 j=1 capsule 的 leading
`(1-1)=0` 外，j>=2 的 capsule 给出负 leading）。IUT 的 variant 应为真，故必须有一处口径
不同：最可能是 **Ind1/literal-min 读法**（ThetaRegion:73-74：literal hull 由 `min_l ord` 控制）
使 qScale 的有效系数从 j^2 降为 j^2 * min_l ord / qOrder —— 若 min 远小于 qOrder，leading 可抵消；
或 A 侧权重/多 place 求和吸收了系数。**GAP-SIGN = 该口径的精确形式**。

## 4. 判定

- `qOrder = n`（I_n），无界；admissible 只给 `l` 不整除 n；**UB 是真缺口**；
- 按源级直接符号（无 Ind1-min 修正）：qScale 为负 leading，`M_lead=(1-sF)A<0`，
  per-capsule j>=2 在 n→∞ 时 `B_i → -inf`（H/ind2 有界：VcI:313-319 给
  `|shellDefect+orderVol| <= sum(3+log e_j)`）⇒ **per-capsule 无条件 FALSE**；
- 若采用 literal-min（Ind1）读法，有效 qScale 系数为 `j^2 * m_i / qOrder`（`m_i = min_l ord(q_{v_l})`），
  leading 可为非负；此时 per-capsule 可对任意 n 成立（但需 `m_i` 的界/结构）——
  **这是把 qpilot 数值 0.025 与 variant 可成立性统一的唯一候选**；
- qpilot 的 0.025（l=5）在该读法下对应 `(qOrder - j^2 m_i)/(2l*qOrder)` 的某组合，需其精确公式。

## 5. 结论与下一步

1. qOrder = n（11a1: 5；858k2: 21；9546f3: 72），整数、无界；
2. admissible 只限制 `l` 不整除 n，无一致界 ⇒ UB 真缺口；
3. 源级直接符号下 qScale 为负、variant leading 为 `(1-sF)A<0`，j>=2 per-capsule 失效；
4. 与 variant 成立性的唯一调和 = literal-min（Ind1）有效系数，需钉死 `m_i` 定义与界；
5. 下一步：读 `thetaComponent`/`thetaFiniteOn` 与 `leastHull` 的 min 实现，确认 literal-min
   是否使 leading 系数变为 `j^2 m_i/qOrder`；若是，写该系数下的 per-capsule 引理；
   若否，variant 的本文形式化陈述与源级符号存在矛盾，需上报。