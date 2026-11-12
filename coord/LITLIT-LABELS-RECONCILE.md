# LITLIT-LABELS-RECONCILE — literal/iv 标签口径与 qpilot 0.025 对齐 (A1014)

| field | value |
|---|---|
| Status | PARTIAL (口径判定：literal=min，iv=单 label；qpilot 0.025 与 literal min 在 l=5 自洽，j>=2 仍需正项/UB) |
| 关键源 | ThetaRegion:34-36 (theta value q_{v_l}^{j²}, q_v = 2l-th root), :58-74 (ivLabels / litLabels；literal hull 由 min_l ord 控制), :52 (Θ_{i,p} 定义) |
| 结论 | α_lit = j² * min_l ord(q_{v_l})；α_iv = j² * ord(q_{v_j})；sign(∂B/∂v_p) = sign(ord_ref - j² min_l ord)；l=5 j=1 且 min/ord=3/4 时恰为 +0.025（qpilot 自洽） |

## 1. 两种读法的定义（lana 源）

- `Iut/Concrete/ThetaRegion.lean:52`: `Theta_{i,p} := prod_c union_{phi in indAut} phi(union_{l in S i} q_{v_l}^{j²} * tensor_l shell_{v_l})`；
- `:58-62` `ivLabels`: `S i = {j}` —— 只用 label j 的 theta value；
- `:63-66` `litLabels`: `S i = S_{j+1}` —— 字面读法；
- `:73-74` 明文："the hull of the literal union is governed by `min_l ord_p(q_{v_l})` rather than the average"。
  这是关键：**literal 的 per-capsule 聚合是 min（对 label l），不是平均、不是逐 label 和**。

## 2. 每 capsule 的精确系数

记 `ord_ref := qOrder w`（A 侧用的 bad place 阶），`m_i := min_{l in S_i} ord_p(q_{v_l})`
（literal）或 `m_i := ord_p(q_{v_j})`（iv，j=i+1）。

qScale（theta 缩放，源链见 ALPHA-DERIVATION §1）：
```
qScale_i = j^2 * m_i * log p / (2l)      (weight-1；一般乘 packetWeight)
A       = ord_ref * log p / (2l)        (无 1/nC)
B_i = A - qScale_i + positive(tame/ind2/arch)
dB_i/dv_p = (ord_ref - j^2 * m_i) / (2l)     -- 关键系数
```

两种读法：
- `ivLabels`：`m_i = ord_p(q_{v_j})`（固定单 label）⇒ `alpha_iv = j^2 * ord(q_{v_j})`；
- `litLabels`：`m_i = min_l ord_p(q_{v_l})` ⇒ `alpha_lit = j^2 * m_i`（**min，不是 j^2/nC**）。

## 3. min 读法下 `1/(2l) - alpha` 的符号

`dB_i/dv_p = (ord_ref - j^2 m_i)/(2l)`。令 `rho_i := m_i / ord_ref`（相对 min 阶）：
```
sign = sign(1 - j^2 * rho_i)      (ord_ref > 0)
positive iff  rho_i < 1 / j^2
```

| j | 需要 rho < | 说明 |
|---|---|---|
| 1 | rho < 1 | 恒成立（只要 min < ord_ref） |
| 2 | rho < 1/4 | min 必须远小于参考阶 |
| 3 | rho < 1/9 | 很苛刻 |
| 4 | rho < 1/16 | ... |

即 **j 越大越难正**；min 读法把 j² 放大后的负项压小，但只有 min 阶足够小才转正。

## 4. 与 qpilot 0.025 对齐

qpilot l=5 的 `A - T = 0.025 * sum v_p log p > 0`。按上面的 literal min 公式：
`j=1` 时 `dB/dv_p = (ord_ref - m_i)/(2l) = (1 - rho)/(2l)`。
l=5（2l=10）：若 `rho = 3/4` ⇒ `(1-3/4)/10 = 1/40 = 0.025` —— **完全吻合**。
因此 qpilot 的 0.025 对应：**literal min 读法、j=1、min_l ord / ord_ref = 3/4**（或等价的聚合口径）。

但其余 capsule（j>=2）按同一公式：`1 - j^2 * rho`；若 rho 仍是 3/4，j=2 给 `1-3 = -2`（斜率 -0.2），
这解释 858k2 的转正需要**正项（tame/ind2/arch）**贡献，而不能只靠斜率。
qpilot 的 2604 全非负是 `K_i + slope*v_p` 的 K_i 足够大（K_i 含 tame/ind2 正项）；
在 v_p 无界时 j>=2 仍会翻负 ⇒ 需要 (UB) 或常数下界 `K_i >= slope_bound * v_p` 的聚合条件。

## 5. 判定与结论

1. **literal 聚合 = min_l**（ThetaRegion:73-74 明文），不是平均、不是逐 label 求和；
2. `ivLabels` 的 per-capsule 系数是 `j² * ord(q_{v_j})`（单 label 固定），不是 min；
3. `litLabels` 的 per-capsule 系数是 `j² * min_l ord(q_{v_l})`，`dB/dv_p = (ord_ref - j^2 m)/(2l)`，
   转正条件 `rho = m/ord_ref < 1/j²`；
4. qpilot 的 0.025 与 literal min、j=1、rho=3/4 完全自洽（l=5）；
5. 若 lana 用 min 读法，j>=2 capsule 的符号依赖 rho 具体值：一般仍为负（除非 min 极小），
   故 **无条件 per-capsule 仍不可得**；需要 (UB) 或把 K_i 正项下界与 slope 合并的聚合引理；
6. 建议：先固定 literal min 读法写 `B_i` 的精确展开（含 m_i, K_i），再把 `rho`/`v_p` 界作为显式假设。

## 6. 下一步

- 读 `InitialThetaData.thetaFiniteOn` 与 hull 的 `leastHull` 实现，确认 min 在体积层如何出现（是否恰好 min 而非 max/交集）；
- 从 qpilot 取得 l=5 的 m_i/ord_ref 数值表，核对 rho=3/4；
- 写 literal per-capsule 精确 Lean 陈述：`B_i = A - j^2 m_i logp/(2l) + K_i`，
  `K_i >= 0` 标注来源；条件引理以 `rho < 1/j^2`（或 v_p 界）为假设。