# SYMBOLIC-INPUTS — M 的精确逐项公式（给 qpilot 符号相消）(A1081)

| field | value |
|---|---|
| Status | READ-ONLY (formulas/definition sources; no Lean written, no compile) |
| 约定 | `A = absLogQ`, `V = logVol(hull vcI)`, `sF = sFactor nC`, `nC = (l-1)/2`, `j = i+1`, `A = logQ/(2l)` |

## 1. A 的展开（exact, no 1/nC）

```
A = sum_w weight_w * qOrder_w * log(p_w) / (2l)          (LeftHandSide:81-88)
A_v = weight_v * qOrder_v * log(p_v)/(2l),  A = sum_v A_v  (exact, no 1/nC)
qOrder_w = (tateParam w).toOrdered.orderNat : Nat         (Basic:171-194; integer)
weight_v 为 place weight（Q.weight，归一化口径）
```
**精确恒等**；`v_p` 为整数 qOrder，非 /2l 归一化（qroot 阶 = qOrder/(2l·e_w)，Data:327-330）。

## 2. V 的展开（1/nC 来自 procession 平均）

```
V = logVol(hull vcI) = (1/nC) * sum_i sum_vQ hullPacket_i(vQ)        (VcI:734-744)
hullPacket_i(vQ) = sum_c packetWeight_i(vQ,c) * componentVol_i vQ c (leastHull(tuple vcIComp))
  其中 hullPacket = packetVol(hull(vcI))；vcIComp = shell/logShell (Ind3:57-62)
packetWeight_i(vQ,c) = prod_j weight vQ (c j)                        (LogVolume:141)
componentVol (tame) = sum_j (1 - 1/e_cj) * log p_v                  (VcI:403-435; exact in tame)
e_cj = ramIdx K (finPart K (c j))                                    (VcI:318/347)
```
**精确恒等**：`logVol_hull_vcI_eq`、`packetVol_product`、tame 公式（tame 条件）；
非 tame 时 `shellDefect = componentVol(leastHull shell) - componentVol(shell)`（VcI:158，signed），
且 `|shellDefect + orderVol| <= sum_j (3 + log e_j)`（VcI:313-319，**上界**，非恒等）。

## 3. gap 的展开（exact + ind2）

```
rhs = processionVol(thetaHull) = (1/nC) sum_i sum_vQ packetVol_i vQ (thetaHull)   (RightHandSide:107)
gap = rhs + sF*A - V                                                        (Gap:521-527, exact)
gap = (1/nC) sum_i sum_vQ gapHullAt_i(vQ)                                   (Gap:895-898/916-935, exact)
gapHullAt_i(finite p) = sum_c tupleWeight p c * ind2Term_i p c              (Gap:895-898)
gapHullAt_i(infinite) = 0
ind2Term_i p c = componentVol(leastHull(thetaComponent))
               - componentVol(scaleElt_i • leastHull(shell))                (Gap:747-754)
gapTerm_finite = shellDefect + ind2Term                                     (Gap:780-783, exact)
thetaComponent = union_{phi in indAut} phi '' (union_{l in S} scaleEltAt l • shell)
                 (ThetaRegion:168-175; iv: S={j}, lit: S=univ)
scaleElt_i = qroot^{j^2}（label factor 内；ThetaRegion:126-139）
```
**精确恒等**：`gap = (1/nC)ΣΣ gapHullAt`、`gapTerm_finite = shellDefect + ind2Term`、
`ind2Term = V(thetaComp hull) − V(scaleElt•hull)`（定义）；
**不等式（非恒等）**：`ind2Term >= 0`（Gap:756）、`gap >= 0`（Gap:514）、
`ind2` 的 frac/有界性（A1022：`ind2 <= frac*logp + O(3+log e)`，frac 项为有界 rounding，非恒等）。

## 4. qScale 的精确值（可符号相消的核心）

```
componentVol (a • O) = - ordp(a) * log p                     (componentVol_units_smul + prod_incl_smul_integral)
ordp(scaleElt) = j^2 * qOrder/(2l * e_w)                     (ordp_qrootOf, Data:327-330; e_w = ramIdx F w)
⇒ qScale_i,v = - j^2 * qOrder_v * log p_v / (2l * e_w)
若 e_w = 1（未分歧）: qScale = - j^2 * A_v
v-scale 求和（j-average）: (1/nC) sum_i j^2 = sF ⇒ 平均 qScale = - sF * A_v
```
**精确恒等**（给定 unit 性 `isUnit_scaleElt` 与 `componentVol_units_smul`）；
这正是 `−(l+1)/24 log q = −sF A` 的来源。

## 5. 可符号相消 vs 不可消

| 项 | 性质 | 说明 |
|---|---|---|
| `A = Σ_v A_v` | 精确恒等 | 无 1/nC |
| `V = (1/nC)Σ_iΣ_v hullPacket` | 精确恒等 | VcI:741 |
| packetWeight 积 | 精确恒等 | LogVolume:141 |
| tame componentVol `Σ(1−1/e)logp` | 精确恒等（tame） | VcI:435 |
| `gap = (1/nC)ΣΣgapHullAt` | 精确恒等 | Gap:895/916 |
| `gapTerm_finite = shellDefect+ind2Term` | 精确恒等 | Gap:780 |
| qScale `−j²qOrder logp/(2l e_w)` | 精确恒等（unit scaling） | Data:330 + units_smul |
| `(1/nC)Σj²/(2l) = sF/(2l) = (l+1)/24` | 精确恒等 | j-average |
| `ind2Term >= 0` | 不等式 | Gap:756 |
| `gap >= 0` | 不等式 | Gap:514 |
| `ind2` frac/有界 | 不等式/rounding | A1022（非恒等） |
| `V(thetaHull) - V(scaled)` 的 q-part | 精确 = qScale | 定义 |

**相消结论**：`A` 与 qScale 的 j-average 可精确相消为 `A - sF A = -(sF-1)A`；
剩余 `V + gap` 中，`V` 的 q-无关部分与 gap 的有界/frac 部分**不可符号相消**（它们是有界项，
除非 gap 含 ∝m 正项——A1022/A1030 已排除）。

## 6. paper Step (v)/(xi) 对应

| paper 公式 | 我们的项 | 性质 |
|---|---|---|
| per-j `− j²/(2l)·log q_{vQ}` | `qScale_i,v` | 精确对应（e=1 时） |
| j-average `−(l+1)/24·log q` | `−sF·A`（因 (l+1)/24=sF/(2l)） | 精确 |
| `(l+5)/4 log d^K + log s^Q + (l+5)l*_mod log s^≤` | `V` 的正部/arch/tame | 部分有界 |
| Step (v) `1/6·log q ≤ ...` | `(l/3)A ≤ ...` | A 上界（非 gap） |
| Step (xi-d) `−|logΘ| ≥ −|log q|` | `gap ≥ (sF−1)A − V` ⇔ variant | 几何（缺） |

## 7. 给 qpilot 的输入表（可直接代入符号计算）

```
符号: nC, l, sF = l(l+1)/12, j = i+1, w_v (place weight), pw(c)=prod_j weight(c j)

A_v      = w_v * qOrder_v * log p_v / (2l)                 [exact]
V_v      = (1/nC) * sum_i sum_c pw(c) * cv_tame(i,v,c)    [exact given tame]
gap_v     = (1/nC) * sum_i sum_c pw(c) * ind2(i,v,c)      [exact given def]
qScale   = - j^2 * qOrder_v * log p_v / (2l * e_w)        [exact; e_w=1 ⇒ -j^2 A_v]
j-average: mean_j qScale = - sF * A_v                     [exact]
M = V + gap - (sF-1) * sum_v A_v                          [def]
```

## 8. 结论

1. 精确可相消：`A_v` 与 qScale 的 j-average（`A − sF A`）；
2. 不可相消（有界/frac）：`ind2`、`shellDefect`、tame 的剩余、`V` 的 q-无关 part；
3. paper 的 `(l+1)/24 = sF/(2l)`、j-average、qScale 与我们的符号**精确对应**；
4. `1/6 log q = (l/3)A` 是 A 的上界，与 gap 无关；gap 的下界仍只能来自 Step (xi-d)；
5. 符号相消的剩余 = `V + gap_bounded − (sF−1)A`，其中负线性项来自 `−(sF−1)A`，
   不能由 bounded gap 抵消（大 m 问题），与 A1022/A1030/A1035 一致。