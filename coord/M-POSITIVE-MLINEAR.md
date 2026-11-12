# M-POSITIVE-MLINEAR — 正 m-线性项：ind2Term 的 +j² 项 (A1020)

| field | value |
|---|---|
| Status | PARTIAL (候选找到：ind2Term 含 +j²·m·logp/(2l)：V(thetaHull) 的 hull 对 contracting 缩放不敏感，而比较项 scaleElt·leastHull 线性下降；精确公式与 GAP-QROOT 待核) |
| 源 | VcI:601-612 (`componentVol_leastHull_tensorLogShell_eq = sum logShellRadius*logp`), :462-472 (`logShellRadius`, `exists_isGreatest_logShellRadius`), :634-640 (`PacketIndexForm`), IdentifiedCopies:67-72 (`componentVol_units_smul`), ThetaRegion:126-139/168-175 (`scaleEltAt`, `thetaFiniteOn`), Gap:747-756 (`ind2Term`) |
| 结论 | ind2Term = V(thetaHull) − V(scaleElt·hull(shell))；V(thetaHull) 与 m 无关（contracting q 的 hull 被未缩放分支支配），V(scaleElt·hull) 含 `−j²·m·logp/(2l)` ⇒ ind2 含 **+j²·m·logp/(2l)** 正 m-线性项，抵消 qScale 的负项后 dM/dm = +logp/(2l) > 0 |

## 1. 两个精确公式（lana 源）

1. `componentVol_leastHull_tensorLogShell_eq`（VcI:601-612，GREEN）：
```
componentVol (.finite p) c (leastHull (tensorLogShell p c))
  = sum_j logShellRadius (finPart K (c j)) p * Real.log p
```
   证明用 `componentVol_prod_incl_smul_integral`（:608）与 `leastHull_tensorLogShell_eq`、
   `exists_isGreatest_logShellRadius`（:469-472：存在最大范数 y，`logShellRadius w p = -ordp K w y`）。
2. `logShellRadius` 定义（VcI:462-465）：
```
logShellRadius w p := sSup ((fun z => -ordp K w z) '' {z in logShell, z != 0})
```
   即 `p^{-rho}·O` 是包含 log-shell 的最小小数理想（fractional ideal）；`rho >= ?` 由 shell 位置定。
3. 缩放版：`componentVol_units_smul`（IdentifiedCopies:67-72）：
```
componentVol (a • X) = componentVol (a • integralAt) + componentVol X   (a 是 unit)
```
   `isUnit_scaleElt`（ThetaRegion:146-149）给出 `scaleElt` 是 unit（Total 环中非零即 unit），
   故可对非整元 `a = qroot^{j²}` 使用；`componentVol (a • integralAt)` 的显式值由
   `componentVol_prod_incl_smul_integral` 型公式给出：**`- sum_j ordp(a_j) * log p`**
   （VcI:608-612 的推导：`componentVol (y • integralAt) = -sum ordp(y_j) logp`，
   取 `y` 为 log-shell 最大范数元时 `-ordp(y) = logShellRadius`）。

## 2. scaleElt 的 m-线性项

`scaleElt = qroot^{j²}` 在 label l（ThetaRegion:126-139），lana 的 `ordp` 是**实数值**
（`-log‖x‖/log p`），无整数性障碍。`qroot` 是 Tate 参数 `q` 的 2l-th root ⇒ `ordp(qroot) = m/(2l)`
（GAP-QROOT：需读 `InitialData.qroot` 定义确认；若为 `m/2` 则系数不同）。
于是：
```
componentVol (scaleElt • integralAt) = - j^2 * m * log p / (2l)      (NEGATIVE, m-线性)
V(scaleElt • leastHull(shell))       = - j^2 * m * logp/(2l) + sum radius logp
```

## 3. thetaHull 对 contracting 缩放不敏感 ⇒ 正项来自 ind2

`ind2Term`（Gap:747-754）：
```
ind2 = V(leastHull(thetaComponent)) - V(scaleElt • leastHull(shell))
```
`thetaComponent`（ThetaRegion:168-175）= `union_{phi in indAut} phi '' (union_{l in S} scaleEltAt l • shell)`。
关键：q 是**收缩**的（bad place，`|q| < 1`，`ordp(q) = m > 0`），故 `scaleElt` 的 `ordp > 0`，
`scaleElt • shell ⊂ shell`（更小）。对 contracting 缩放：
- 每个 factor 上，`leastHull (shell ∪ a_k • shell) = leastHull(shell)`（因为 `a_k•shell ⊂ shell`）；
- `indAut` 是格自同构，保 covolume，作用后 hull 的**体积不变**；
- 故 `V(leastHull(thetaComponent))` 的 leading 与 `V(leastHull(shell))` 相同，**与 m 无关**
  （只有 `O(radius, 3+log e)` 的有界修正）。

因此：
```
ind2 = [m-independent: V(hull(shell)) + bounded] - [-j^2 m logp/(2l) + radius terms]
     = + j^2 * m * logp/(2l) + (bounded)
```
**即 ind2Term 含 `+j²·m·logp/(2l)` 的正 m-线性项**（每 capsule i 取 `j = i+1`）。
这与 `ind2Term_nonneg`（Gap:756）一致，并且正好补偿 qScale 的负项。

## 4. 净 m-线性系数

per capsule i（单 place, weight 1）：
```
B_i = A + [qScale: -j_i^2 m logp/(2l) + bounded] + [ind2: +j_i^2 m logp/(2l) + bounded] + arch
    = A + bounded
dM/dm = (1/nC) * sum_i dB_i/dm = (1/nC) * sum_i (logp/(2l)) = logp/(2l)  > 0
```
即 **M 的净 m-线性系数 = +logp/(2l) > 0**（单 place；A 的 +1 项由 ind2 的 +j² 抵消 qScale
后留下的正是 A 本身；更准确：qScale 与 ind2 的 j² 精确相消，M 的 m-线性部分 = A）。
多 bad places / weights 时按 place 求和：`dM/dm = sum_v weight_v logp_v/(2l) > 0`。

## 5. 结论

1. `componentVol_leastHull_tensorLogShell_eq = Σ logShellRadius·logp`（GREEN，VcI:603-612）；
2. `logShellRadius`（VcI:462-472）由 log-shell 最大范数元定义；
3. `scaleElt = qroot^{j²}` contracting ⇒ `componentVol(scaleElt·O) = −j²·m·logp/(2l)`（m-线性负）；
4. 但 `V(thetaHull)` 与 m 无关（hull 被未缩放分支支配），故 **ind2Term = +j²·m·logp/(2l) + bounded**
   （正 m-线性，且 ind2Term_nonneg GREEN）；
5. 净 M 系数 = `+logp/(2l) > 0` ⇒ **M→+∞ as m→∞**，`dM/dm>0`，大 m 反例消失；
6. 这与 qpilot 的数值方向一致（v 增大更强）；A1018 的 `dM/dm=1−sF` 是因为漏掉了 ind2 的
   `+j²` 正项（把 thetaHull 当成了 scaled hull）；
7. GAP-QROOT：`ordp(qroot) = m/(2l)` 需读 `InitialData.qroot` 定义确认；若为 `m/2`
   则系数变化但正负抵消结构不变（仍 +j² 正项与 qScale 同系数）。

## 6. Lean 陈述草案

```lean
/-- Scaling element volume: componentVol (a • O) = -j^2 * m * logp / (2l). -/
def scaleVol (j m logp l : Real) : Real := - (j ^ 2) * m * logp / (2 * l)

/-- theta hull leading is m-independent; ind2 contains the positive compensation. -/
def ind2Leading (j m logp l : Real) : Real := (j ^ 2) * m * logp / (2 * l)

/-- Net per-capsule m-linear coefficient: scale + ind2 cancel, leaving the A term. -/
theorem net_mLinear (j m logp l : Real) :
    scaleVol j m logp l + ind2Leading j m logp l = 0 := by
  unfold scaleVol ind2Leading; ring

/-- M leading = A = m logp/(2l), so dM/dm = logp/(2l) > 0. -/
theorem dMdm_pos (m logp l : Real) (h : 0 < logp) (hl : 0 < l) :
    0 < logp / (2 * l) := by positivity
```
（真实文件应把 `scaleVol` 与 `ind2Leading` 接到 `componentVol_units_smul` 与 `ind2Term`
的实际展开；`net_mLinear` 是纯算术骨架。）

## 7. 待办

1. 读 `InitialData.qroot` 定义，钉死 `ordp(qroot) = m/(2l)`（GAP-QROOT）；
2. 读 `componentVol_tensorLogShell_eq`（VcI:794 区域）与 `componentVol_prod_incl_smul_integral`
   的精确符号，确认 `componentVol(a·O) = −Σ ordp(a_j)logp`；
3. 用 green `leastHull_units_smul`、`leastHull_mono`、`ind2Term_nonneg` 写 `ind2Term` 的
   精确 m-线性展开；
4. 与 A1018 的 `dM/dm=1−sF` 分歧上报：A1018 遗漏 ind2 正项，应以本文件为准（待 GAP-QROOT
   与符号确认后）。