# M-MLINEAR-TERMS — M 展开中随 m=v_p(q) 线性增长的项与符号 (A1018)

| field | value |
|---|---|
| Status | PARTIAL (m-linear 项清单完成；dM/dm 符号取决于 effective theta 系数；平均值读法下为大 m 反例，literal-min 读法下抵消项出现) |
| 源 | `IdentifiedCopies:441-456` (`logVol_lgp_integral = -sF*absLogQ`, GREEN), LeftHandSide:81-88, VcI:741, Gap:747-756/909-935, VcI:313-319 (shellDefect 界), ThetaRegion:58-74 (min 读法) |
| 结论 | A 项 +1；`logVol_lgp_integral` 与 qScale 为负（−sF / −j²）；ind2/shellDefect 有界、非 m 线性；平均读法 `dM/dm=(logp/2l)(1-sF)<0`（大 m 反例）；唯一抵消 = literal-min(Ind1) 使 effective 系数降为 min j²=1 ⇒ dM/dm=0 |

## 1. 所有随 m 线性增长的项（M = (1/nC)Σ_i B_i 展开）

记 `A = m*logp/(2l)`（单 place, weight 1），`sF = sFactor nC = Σ_j j²/nC = l(l+1)/12`。

| 项 | 表达式 | m-线性系数 | 来源/状态 |
|---|---|---|---|
| A（q-side） | `+m logp/(2l)` | **+1/2l** | LeftHandSide:81-88（GREEN） |
| `logVol_lgp_integral` | `-(sFactor nC) * A = -sF*m logp/(2l)` | **-sF/(2l)** | IdentifiedCopies:441-456（GREEN，明确 `-sF*absLogQ`） |
| qScale (per capsule, 平均前) | `-j^2*m logp/(2l)` | -j²/(2l) | ThetaRegion:34；unit scaling |
| theta hull leading（平均后） | `-sF*m logp/(2l)` | -sF/(2l) | Gap:909-935 + 平均 |
| ind2Term | `>= 0`，但 `<= sum(3+log e_j)` 级别 | **0（有界，非 m 线性）** | Gap:747-756 非负；VcI:313-319 同类界 |
| shellDefect | `|shellDefect+orderVol| <= sum(3+log e_j)` | **0（有界）** | VcI:313-319 |
| orderVol | `<= 0`，亦在同上界内 | **0（有界）** | VcI:102/313-319 |
| archDefect/shellDefect 常数 | `>= 0`，常数 | 0 | Gap:442/463 |
| e 依赖 | `e = 2l/gcd(2l,m) in {l,2l}`，H=(1-1/e)logp | 0（两值、有界） | VcI:347/403-415；E-V-DEPENDENCE |

**结论：lana 源中唯一的两个 m-线性项是 +A 与 −sF·A（等价地 −sF*A 与 −j² per capsule）；
没有第三个独立的 m-线性正项。** ind2/shellDefect/orderVol 都只有 `O(3+log e)` 的界。

## 2. dM/dm 的精确表达式

平均（literal S_i 全 label）读法：`M = A + rhs`，`rhs = -sF*A + (bounded positives)`，
```
dM/dm = (logp/(2l)) * (1 - sF).
```
l=5: sF=2.5 ⇒ `(logp/10)*(-1.5) < 0`；l>=5 恒 `sF = l(l+1)/12 > 1` ⇒ **dM/dm < 0**。
故平均读法下 m→∞ 时 `M -> -inf`（inding/arch 有界），**存在大 m 反例**；
qpilot 的 2604/21,027 全非负只是 m 有界的枚举。

literal-min（Ind1）读法：有效 theta 系数为 `m_eff = min_l j_l²`（hull 由 min ord 控制，
ThetaRegion:73-74）；若 min 落在 `j=1` 的 label：
```
rhs_lead = -1 * m logp/(2l)   (effective coefficient 1)
M_lead = A + rhs_lead = 0    => dM/dm = 0,  M = bounded positives >= 0
```
此时「抵消正项」不是独立的新项，而是**把平均 sF 降为 min j²=1 后的差值 `(sF-1)*A`**，
来自 (Ind1)/literal-min 的 hull 选择，不在 lana 的 `logVol_lgp_integral` 平均式中。

## 3. 判定：若 dM/dm<0，抵消它的正项在哪？

- **平均读法下不存在抵消项**：lana 源无第三个 m-线性正项（见 §1 表）；ind2 的 nonneg
  是 `O(1)` 级的，不随 m 增长；因此平均读法配上任意大的 m 会给出 `M < 0`，
  **与 variant 对一般 admissible 数据成立矛盾**；
- **唯一自洽解释 = literal-min(Ind1) 读法**：`logVol_lgp_integral` 的 `-sF*A` 是 LGP·O
  （integral region，体积 0）的平均体积，而 theta-pilot 的 hull 经 Ind1 可以选择最小
  label 的 q 幂（hull of literal union 由 `min_l ord` 控制），使有效系数从 sF 降到 min j²；
  若 min j²=1，M 的 m-线性部分精确抵消（`A - A = 0`），M 只剩有界正项 ≥0；
- 因此**不是**「paper 有一个隐藏正项」，而是**平均式与 min 式的差别 `(sF-1)A`**；
  形式化必须用 literal-min 读法，否则大 m 反例成立。

## 4. 与 qpilot 数值的对应

- qpilot 的 0.025（l=5）与 min 读法下 `(1 - m_eff/m)/(2l)`（ρ=m_eff/m）一致（见
  LITLIT-LABELS-RECONCILE §4）；
- 平均读法给出系数 `1-sF = -1.5`（l=5），与 0.025 不符 ⇒ 数值也支持 min 读法；
- 但 min 读法下 j>=2 capsule 的 `j²*min/m` 仍可能 >1，故 per-capsule 仍需 m=1 的 min 结构；
  聚合 M 的 m-线性系数为 `1 - min_l`，若 min 取到 j=1 则 =0。

## 5. 结论/下一步

1. m-线性项仅两类：`+A` 与 `−sF·A`（GREEN `logVol_lgp_integral`）；ind2/shell/order 有界；
2. 平均读法 `dM/dm = (logp/(2l))(1-sF) < 0`（l>=5）⇒ 大 m 反例；lana 无补偿正项；
3. 唯一补偿 = literal-min(Ind1) 的 effective 系数 `min_l j²`；若 min=1 ⇒ dM/dm=0、M≥0 由有界项；
4. 形式化路线：用 literal-min 读法重写 per-capsule 的 qScale 系数为 `j² * m_eff`，
   并把 `m_eff <= (sF)*m`（或 min=1 的 label 存在性）作为引理/显式假设；
5. 若坚持平均读法，则必须承认大 m 反例并放弃无条件 variant —— 需上报 lead 决策。