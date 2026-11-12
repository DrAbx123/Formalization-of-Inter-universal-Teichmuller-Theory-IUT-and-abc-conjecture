# PER-CAPSULE-PROOF-PLAN — 从数值事实到可证局部算术命题 (A1010)

| field | value |
|---|---|
| Status | PARTIAL (定义钉死；纯算术形式给出；无条件引理 **尚不可证**，需一致 q-order 界) |
| 数值输入 | qpilot: admissible 2604 全部 `A + H_i >= 0`（min 2.51/3.03 strict split；uniform min 5.30），858k2 转正 |
| 判定 | 2604 是有限枚举数值证据，不是证明；需 (UB) 一致界 + (COEF) 精确系数识别才能成为引理 |
| 版本钉住 | lana 根 Iut/ 树 + 行号；未编译 |

## 1. `ord_v(q_v)` / `qOrder` 的精确定义（lana 源）

- `qOrder` = `Iut.InitialThetaData.qOrder`（见 `Iut/Cor312/ThetaData/AdmissiblePrime.lean:52`：
  "its normalized integer order is `Iut.qOrderAt` (`Iut.InitialThetaData.qOrder`), independent of
  the uniformizer of `F_w` used to normalize it"）；底层是 Tate 参数 `tateParameterAt` /
  `InitialThetaData.tateParam` 的归一化整数阶 `orderNat`，`orderNat_eq_qOrderAt` 给出 uniformizer
  无关性；`InitialThetaData.coprime_qOrder` 记录 ℓ 与其阶互素。
- 定义 3.1(c)（AdmissiblePrime.lean:152 附近）字段 `q_order_coprime`：
  `forall w in badPlaces, forall t : TateParameter ..., forall pi uniformizer,
   (t.toOrdered hpi).PrimeToOrder l` —— 即 **l 与 ord_pi(q) 互素**（不是界！）。
- `LeftHandSide.lean:81-84`: `logQ := sum_{w in badFinset} Q.weight w * (qOrder w ... : Real)
  * Real.log (residueChar w)`；`:88` `absLogQ := logQ/(2*l)`。

**归一化裁定**：`v_p(q) := qOrder w` 是**实际整数阶**（不是 `v_p(Delta)`，也不是 `v_p/(2l)`）；
`A_v = weight_v * v_p(q) * log p_v / (2l)`，`A = sum_v A_v = logQ/(2l)`（无 1/nC）；
`v_p(Delta)` 与 `v_p(q)` 的关系：乘法退化时 `v_p(Delta) = -v_p(j)` 与 Tate 参数阶不同，
论文左端用的是 `ord_w(q_w)`（即 `qOrder`），**不是** `v_p(Delta)`；这一点必须固定在定义层。

## 2. `PerCapsuleBound` 的纯算术形式

按 `DECOMP-NORMALIZATION.md` 的唯一展开 `M = (1/nC) * sum_i (A + H_i)`，
`PerCapsuleBound` 即
```
forall i, 0 <= A + H_i,
A = sum_{v finite} weight_v * v_p(q) * log p_v / (2l),      -- 全局，无 1/nC
H_i = sum_{v} sum_{c} packetWeight(i,v,c) * componentVol(i,v,c),   -- 每 capsule 局部
```
把 `componentVol` 按 lana 源展开：tame finite（`VcI.lean:435`）
```
componentVol^{tame}(i,v,c) = sum_{j} (1 - 1/e_{cj}) * log p_v   >= 0
```
q-scaling 项（theta 单位缩放，hull DECOMP-R-LOCAL §2）
```
qScale(i,v) = (1/(2l)) * sum_{j} j^2 * v_p(q) * log p_v   (= sF * A_v 若 e=2l 归一化匹配)  -- 符号/系数待 (COEF)
```
其余正项：`ind2Term >= 0`（Gap.lean:756）、`archDefect >= 0`（Gap.463）、`shellDefect >= 0`（Gap.442）。

于是纯算术形式（草案）：
```lean
/-- Per-capsule arithmetic bound: A + tame + ind2 + arch >= qScale. -/
def PerCapsuleArith (A tame ind2 arch qScale : Real) : Prop :=
  qScale <= A + tame + ind2 + arch

theorem perCapsule_of_arith (h : PerCapsuleArith A tame ind2 arch qScale) :
  0 <= A + (tame + ind2 + arch - qScale) := by linarith
```
展开到 (v,i,c,j)：`tame = sum_v sum_c packetWeight * sum_j (1 - 1/e_cj) log p_v`，
`qScale = sum_v sum_c packetWeight * (1/(2l)) * sum_j j^2 * v_p(q) * log p_v`；
arch/ind2 为相应正项。

## 3. 使 `PerCapsuleArith` 成立所需假设与来源

1. **(COEF) 精确系数识别**：`qScale` 的 `j^2` 和、`e = 2l`、`1/(2l)` 位置必须与 qpilot
   的精确 Kummer 重算一致；A1008 已钉死 1/nC 位置（A 无、H_i 局部、外层 1/nC），
   但 `qScale = sF * A_v` 的**系数**仍需用 `sum_jsq_eq_nC_mul_sFactor`
   (Mzk1ScalingNormalizationActual) 在具体 label 集/权重下验证。**状态: GAP-COEF**。
2. **(LABEL) label 权重归一**：`sum_c packetWeight = sum_c prod_j weight = 1`（LogVolume:141/153），
   保证 tame 正项按权重平均；GREEN。
3. **(E) ramification 取值**：`e_cj = 2l` 的精确 Kummer 情形需 `e >= 1`；若某 c 的
   `e_cj = 1`（未分歧）则 `1 - 1/e = 0`，正项消失——需逐 label 假设。**GAP-E**。
4. **(ARCH) 无穷位**：`archDefect >= 0`（Gap:463）与 paper `log(sqrt 2 * pi)` 等价**未证**
   （GAP-A，见 DECOMP-NORMALIZATION）。
5. **(UB) v_p 的一致界**（关键）：若 admissible 允许 `v_p(q)` 任意大，则 `qScale` 线性增长
   而 `A + tame + ind2` 有界 ⇒ 不等式失效。定义 3.1 只给 `l` 与 `v_p(q)` 互素
   （`q_order_coprime`），**没有**一致界；一致界必须来自：
   (a) 有限坏集 + Θ-data 的 conductance/高度界；或 (b) 对 admissible 族的额外定义（如
   `|v_p(q)| <= B_p` 作为 admissible 条件）。**当前 lana 源中未找到 (UB)**；
   这是本引理不可无条件化的唯一实质缺口。**GAP-UB**。

## 4. 结论：能否得到无条件的 per-capsule 算术引理？

**不能**（以当前 Definition 3.1/admissible 数据为范围）：
- 逐位形式与 1/nC 位置已钉死；tame/ind2/arch 的独立非负来源 green-by-source；
- 但 `qScale` 随 `v_p(q)` 线性增长，而 `A + tame + ind2` 对 `v_p(q)` 无控制；
- `l` 与 `v_p(q)` 互素（`q_order_coprime`）不提供界；
- qpilot 的 2604 全部非负是**特定有限数据/界下的枚举**，不能替代一致界引理。

**可做的条件引理（推荐下一步）**：
```lean
theorem perCapsuleArith_of_bound
    (A tame ind2 arch qScale : Real) (hp : 0 <= tame + ind2 + arch)
    (h : qScale <= A) : 0 <= A + (tame + ind2 + arch - qScale) := by linarith
```
其中 `h : qScale <= A` 就是 (COEF)+(UB) 的合并形式（在 e=2l 归一化下即 `v_p(q) <= ...`）；
把 (UB) 写成 `v_p(q) <= B_p` 的显式假设字段，登记为 class-B 外部输入，即可得到条件引理。

## 5. 待办

1. 用 qpilot 的精确 Kummer 公式替换 §2 的 `qScale` 草案（(COEF)；先验证 `sF` 与 `e=2l` 系数）；
2. 找/定义 (UB) 来源：坏集有限性 + Θ-data 高度界，或写入 admissible 定义；
3. (UB)+(COEF) 后写 `Mzk1PerCapsuleArithActual.lean`：纯算术条件引理 + 具体 label 求和展开；
4. 数值 2604 记录为 NUMERIC 证据，不进入 PROVED 计数。