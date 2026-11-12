# ALPHA-DERIVATION — qScale 系数的 lana 源推导 (A1013)

| field | value |
|---|---|
| Status | PARTIAL (源级推导完成；与 qpilot 的 0.025 存在口径矛盾，需其精确公式核对) |
| 关键源 | ThetaRegion:34-36 (theta value `q_{v_l}^{j²}`, `q_v` = 2ℓ-th root of Tate), Container:220-231 (scaleElt 单 label), IdentifiedCopies:67 (`componentVol_units_smul`), ScaleVolume:20 (`κ(p) = -log p`), ThetaRegion:73-74 (literal hull uses min_l ord) |
| 结论 | 字面（单 label）qScale 系数 `alpha = j²` ⇒ `dB/dv_p = (1-j²)/(2l) <= 0`（j=1 为 0，j>=2 为负）⇒ **j>=2 需 UB**；qpilot 0.025 无法从该字面形式直接得到 |

## 1. lana 源链（逐行）

1. `Iut/Concrete/ThetaRegion.lean:34-36`：capsule `S_{j+1} = {0,...,j}`（`j = i+1`），
   theta value 是 `q_{v_l}^{j²}` 放在第 `l` 个 tensor factor；**`q_v` 是 Tate parameter 的
   2ℓ-th root**（IUT I, Example 3.2(iv)）。故
   `ord(q_v) = ord(q_Tate)/(2l)`（在整数/归一化阶意义下；2ℓ 因子进入这里）。
2. `Iut/Arakelov/Container.lean:220-231`：`scaleElt` 把 `(a i).elt` 放入**单个 label
   `lab i` 的 tensor factor（`LocalTheory.incl ... (lab i)`），`isUnit_scaleElt`。
3. `Iut/Wall/IdentifiedCopies.lean:67` `componentVol_units_smul`：
   `mu^log(a·X) = mu^log(a·O) + mu^log(X)`；
   `Iut/Concrete/LocalConstruct/ScaleVolume.lean:20`：`κ(p) = -log p`
   （`componentVol_prime_preimage'`）。故单位 `a`（order `ord(a)`）作用于体积 =
   `- ord(a) * log p`。
4. `Iut/WallEquiv/VcI.lean:183` `haar_units_smul`（同一 scaling law 的 Haar 版）；
   `Iut/WallEquiv/Gap.lean:709` `unfold InitialThetaData.scaleElt scaleEltAt`。
5. `Iut/Concrete/ThetaRegion.lean:58-74`：两种 (Ind1) 读法 —— `S i = {j}` (`ivLabels`)
   与 `S i = S_{j+1}` (`litLabels`)；**literal union 的 hull 由 `min_l ord_p(q_{v_l})`
   控制，而不是平均值**（:73-74）。

## 2. qScale 的精确系数

单 label 字面情形（`ivLabels`, capsule i, label l=j）：缩放元 order`= j² * ord(q_v) =
`j² * ord(q_Tate)/(2l)`，其体积贡献：
```
qScale(i,j) = j^2 * ord(q_Tate) * log p / (2l)   (weight factor 1)
            = j^2 * A_v,   A_v := ord(q_Tate) * log p / (2l).
```
故 qScale 的 A-单位系数：
```
alpha(j) = j^2,     dB_i/dv_p = (1/(2l)) * (1 - j^2).
```
`j = 1`（capsule S_2）⇒ 0；`j >= 2` ⇒ 负（l=5: j=2 ⇒ -3/10；l=7: j=2 ⇒ -3/14, j=3 ⇒ -8/14；
l=11: j=2..5 ⇒ -3/22, -8/22, -15/22, -24/22；l=13: 到 j=6 ⇒ -35/26）。

注意 weight 因子：一般 `qScale = (prod_l weight_l) * j² * ord(q_Tate) * log p/(2l)`，
`A_v` 用 place weight `weight_v`；系数按 weight 比例缩放，不改变符号结构。

## 3. 符号表：`1/(2l) - alpha`

假设单 label 字面形式 alpha = j²（A-单位）：

| l | nC | j | alpha=j² | `dB/dv_p = (1-j²)/(2l)` |
|---|---|---|---|---|
| 5 | 2 | 1 | 1 | 0 |
| 5 | 2 | 2 | 4 | **-3/10 = -0.30** |
| 7 | 3 | 1 | 1 | 0 |
| 7 | 3 | 2 | 4 | **-3/14 ≈ -0.214** |
| 7 | 3 | 3 | 9 | **-8/14 ≈ -0.571** |
| 11 | 5 | 1..5 | 1,4,9,16,25 | 0, -3/22, -8/22, -15/22, -24/22 |
| 13 | 6 | 1..6 | 1,4,9,16,25,36 | 0, -3/26, -8/26, -15/26, -24/26, -35/26 |

结论：**字面单 label 形式下，仅 j=1 的 capsule 系数为 0，j>=2 全部为负** ⇒ v_p 增大时
B_i 最终为负 ⇒ 需要 (UB) 或正项（tame/ind2/arch）的定量下界。

## 4. 与 qpilot 数值的核对

qpilot l=5 称 `A - T = 0.025 * sum v_p log p > 0`。按本推导：
- j=1: 系数 0；j=2: 系数 -0.30（A-单位）或 -0.4（qScale 直接/2l 单位）；
- 0.025 不对应任何 `(1-j²)/(2l)`（j=1 给 0，j=2 给 -0.3/-0.4）；
- 若把 `A` 记作 `v_p logp/(2l)` 且 qScale 记作 `j² v_p logp/(2l)`，则 `A - qScale = (1-j²)v_p logp/(2l)`，
  同样非正（j>=2）。
⇒ qpilot 的 0.025 必来自**额外正项或不同归一化**：可能 (i) tame 项 `(1-1/e)logp` 的
常数被并入并抵消了 v_p 斜率后的 net 系数；(ii) 其 `T` 定义已是聚合/平均（含 1/nC 或 label 平均）；
(iii) `q_v` 的 2ℓ-root 在其数值模型中归一化不同。需 qpilot 给出精确 α 公式核对。
**GAP-COEF：qpilot 0.025 与源级 alpha=j² 不一致。**

## 5. 结论

1. 源级字面 alpha(j)=j²（单 label，weight-1），`dB/dv_p = (1-j²)/(2l)`：j=1 为 0，j>=2 为负；
2. 因此 **字面 per-capsule 对 j>=2 需 UB 或正项定量下界**，不能无条件；
3. literal hull 用 `min_l ord`（ThetaRegion:73-74，最有利的 label）可能把有效 j 降为 1
   —— 若 hull 的 min 落在 j=1 的 label，则字面 per-capsule 系数为 0，需正项常数 >= 0；
   ivLabels 单 label 读法不能享受这个 min；
4. qpilot 的 0.025 与 alpha=j² 矛盾，标 GAP-COEF，需其精确 Kummer 公式；
5. 无条件化的两个候选：(a) 聚合（literal min 读法 + tame 常数下界）；(b) (UB) 显式假设。

## 6. 下一步

- 请 qpilot 给出 `A-T` 的逐项公式（含 e=2l, label 数, 1/nC, weight）以核对 0.025；
- 若是 (ii) 聚合口径，则改写 per-capsule 为聚合引理（min_l 或 sum_l 平均）；
- 若维持单 label 字面，则写 (UB) 条件引理：`forall p, v_p(q) <= B_p` ⇒ B_i>=0。