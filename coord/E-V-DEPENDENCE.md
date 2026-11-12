# E-V-DEPENDENCE — e 与 qScale 的 v 依赖 (A1015)

| field | value |
|---|---|
| Status | PARTIAL (e(v) 已钉死；qScale 的 v 依赖耦合已给出；R 侧符号方向仍 GAP-SIGN) |
| 源 | VcI:318/347/359 (`ramIdx`), VcI:403-415 (tame 公式 `sum_j (1-1/e_j) log p`), ThetaRegion:34-36 (q_v = 2l-th root of Tate), IdentifiedCopies:67 (units_smul), ScaleVolume:20 (kappa(p)=-log p), Gap:747-756 (ind2Term) |
| 结论 | `e(v) = 2l/gcd(2l,v)` ∈ {l, 2l}（因 Def 3.1(c) `l` 与 ord 互素 ⇒ gcd(2l,v) | 2）；H 有界、不随 v 增长；qScale ∝ v·g；v→∞ 时 B_i 的性态由 R 侧符号决定（GAP-SIGN）：若缩放项进 RHS 为负 ⇒ j>=2 时 B_i → -inf（per-capsule 无条件 FALSE） |

## 1. e 作为 v 的函数

- lana 的 e 是 `ramIdx K (finPart K (c j))`（VcI:318、:347、:359 `ramIdx_pos'`），即 K/F 的
  分歧指数；tame 公式 `neg_sum_ordp_scalA_tame`（VcI:403-411）：
  `-(sum_j ordp K (finPart K (c j)) (scalA c j)) * log p = sum_j (1 - 1/e_j) * log p`；
- Kummer 构造（ThetaRegion:34-36）：`q_v` 是 Tate parameter 的 **2l-th root**，K = F(q^{1/(2l)})；
  标准 Kummer 分歧：`e = 2l / gcd(2l, v)`，其中 `v = ord_w(q_Tate)`；
- Def 3.1(c) `q_order_coprime`（AdmissiblePrime:152）：`l` 与 `v` 互素 ⇒ `gcd(2l, v) | 2`，
  故 **`e(v) ∈ {l, 2l}`**，具体
  `g := gcd(2l, v) ∈ {1,2}`，`e = 2l/g`：
  - `v` 奇（g=1）：e=2l（最大分歧）；
  - `v` 偶（g=2）：e=l（分歧折半）。
**e 不是 `2l/gcd(2l,?)` 随 v 连续增长，而是只取 l 或 2l 两个值**（v 的奇偶）。

## 2. H 的显式公式

tame `H = sum_{labels} (1 - 1/e) * log p = sum_{labels} (1 - g/(2l)) * log p`：
- g=1: 每 label `(1 - 1/(2l)) log p`；g=2: `(1 - 1/l) log p`。
标签数 = capsule S_{j+1} 的 label 数 = j+1（ThetaRegion:31-32）。
因此 **H 与 v 无关（只经 g∈{1,2} 取两值），有界**：`H <= (j+1) log p`。

## 3. qScale 的精确 v 依赖

`q_v = q_Tate^{1/(2l)}` 在 K 中的阶：`ord_K(q_v) = v/e = v·g/(2l)`（归一化阶）。
theta value 在 label l 的幂 `q_v^{j²}`（ThetaRegion:34）：
```
qScale_i = j^2 * ord_K(q_v) * log p = j^2 * v * g * log p / (2l),
A       = v * log p / (2l)              (base field order; 无 1/nC)
```
两者组合的净系数（若缩放项进入 B_i 为负号，见 GAP-SIGN）：
```
B_i = (v log p/(2l)) * (1 - j^2 * g) + H_i(g) + ind2_i(v) + arch
dB_i/dv = (log p/(2l)) * (1 - j^2 * g)
```
- j=1, g=1: 斜率 0 ⇒ B_i = H + ind2 + arch >= 0（**无条件**，只要 H/ind2/arch>=0）；
- j=1, g=2: 斜率 -1·(logp/2l) < 0 ⇒ v→∞ 需 ind2/常数抵消 ⇒ 需 UB；
- j>=2, g∈{1,2}: 斜率 <= -3(logp/2l) < 0 ⇒ v→∞ **B_i → -inf**（H/ind2 有界，ind2 的
  `frac` 依赖 g 但 VcI:313-319 给 |shellDefect+orderVol| <= sum(3+log e_j) 有界）。

## 4. v→∞ 行为（两符号情景）

**(i) 若缩放项进 B_i 为负（componentVol 分析：a=q^{j²} 收缩，`μ(a·O) = -ord(a)logp < 0`；
ind2 = V(thetaHull) - V(scaled shell) >=0 只给差值）**：
- j=1,g=1: B_i 有界且 >=0（H+ind2+arch）；
- j=1,g=2 或 j>=2: **B_i → -inf** ⇒ per-capsule 对任意 admissible v **FALSE**，
  不只是缺 UB；qpilot 的 2604 全非负只说明其枚举范围 `N<=9999`/`v` 有界内成立。

**(ii) 若缩放项进 B_i 为正（i.e. R 侧 = -rhs 使 scaled-shell 项整体反号）**：
- 则 `dB_i/dv = (1 + j^2 g)/(2l) > 0` ⇒ v→∞ B_i → +inf，per-capsule **无条件 TRUE**
  （但需 H/ind2/arch 非负，green-by-source）。
两者结论相反；**GAP-SIGN** = 缩放项在 `R = -rhs` 中的符号，必须由 `componentVol_units_smul` +
`kappa(p) = -log p` + `leastHull` 与 `thetaHull` 的方向逐符号确认（本任务预算内未定）。

## 5. 与 qpilot 的对齐

- qpilot 的 0.025（l=5）在情景 (i) 的 j=1,g=1 下应为 0 而非 0.025；在情景 (ii) 下应为
  `(1+g)/(2l)=0.2`（j=1,g=1）而非 0.025 ⇒ **两个纯 Kummer 情景都不给 0.025**；
- 0.025 更可能来自 weight/归一化（如 `(1 - rho)/2l`, rho=3/4，见 LITLIT-LABELS-RECONCILE）
  或 qpilot 的 v 定义（已含 1/(2l)）——需其精确公式核对；
- 但 **v 依赖的定性结论不依赖 0.025**：e 只有两个值；H 有界；qScale ∝ v·g；因此 j>=2 的
  性态由斜率符号决定，必须钉死 GAP-SIGN 才能判定无条件性。

## 6. 结论

1. `e(v) = 2l/gcd(2l,v)`，由 Def 3.1(c) 得 g ∈ {1,2}，故 e ∈ {l,2l}；H 有界、两值；
2. `qScale = j^2 v g logp/(2l)`，`A = v logp/(2l)`；净斜率 `(1 - j^2 g)/(2l)`（情景 (i)）；
3. v→∞：j=1,g=1 ⇒ 有界非负；j>=2（或 g=2 的 j=1）⇒ -inf（情景 (i)）；
4. **GAP-SIGN 未定**：若 (ii)，全部 j 的 v→∞ 都是 +inf ⇒ per-capsule 无条件 TRUE；
5. 在此之前不能断言 per-capsule 无条件；qpilot 有限枚举 N<=9999 不覆盖 v→∞。

## 7. 下一步

1. 钉死 GAP-SIGN：读 `proj_hull_thetaPilot`（Gap:909-）与 `componentVol_units_smul`、
   `ind2Term` 定义，确认 thetaHull 的 log-vol 中 `q^{j²}` 项的符号；
2. 若 (i)：写 `PerCapsuleFalse` 反例形式（v 足够大）或加显式 UB；
3. 若 (ii)：写无条件 per-capsule 引理（线性正系数 + H/ind2/arch 非负）；
4. 用 qpilot 精确公式核对 0.025（当前与两种 Kummer 情景均不符）。