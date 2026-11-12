# FAITHFUL-E-GROWTH — ind2Term / gap 随 qOrder 的解析增长

日期：2026-11-13；qpilot（A1115）。**只写文档/SymPy**；未编译。源码：`tmp/external/ported/lana_tgfree/`（完整 lana 源；`lana_core` 是子集）。

## 1. 源码链

| 事实 | 文件:行 | 陈述 |
|---|---|---|
| `ind2Term` | `Iut/WallEquiv/Gap.lean:748-755` | `V(hull(θComp)) − V(scaleElt • hull(shell))` |
| `thetaComponent` | `Iut/Concrete/ThetaRegion.lean:127-140, 171-176, 252-260` | `scaleEltAt l = incl_l(qroot^{j²})`, `scaleElt = scaleEltAt distinguished`; `thetaFiniteOn = ⋃_{φ∈indAut} φ '' (⋃_l scaleEltAt l • shell)`; `thetaComponent = thetaComponentOn ivLabels` |
| `ord(scaleElt)` | `Iut/Concrete/ThetaLocalConstruct/Data.lean:327-331` | `ordp(qrootOf v) = qOrder/(2ℓ·ramIdx)`; 因而 `ord(scaleElt) = j²·qOrder/(2ℓ·e)`, `e=ramIdx` |
| `leastHull_units_smul` | `Iut/WallEquiv/Gap.lean:149-150` | `leastHull(s • U) = s • leastHull U` for unit s |
| 单位缩放体积 | `Iut/Wall/IdentifiedCopies.lean:68-73`, `Iut/Concrete/LocalConstruct/ScaleVolume.lean:53-55,119-123` | `V(a•X)=V(a•integral)+V(X)`; 单因子 `a=incl_l(y)`: `V(a•integral)=−ordp(y)logp` |
| `prop14_iii` | `Iut/Concrete/LocalConstruct/Theory.lean:309-327` | 所有 `φ∈indAut` 的 `φ(incl_l(x)•shell)` 落在某个 `a•integral` 中，且 `V(a•integral) ≤ (−ordp x+Σ_i d_i+1)logp + ram terms` |
| `gapTerm_finite` | `Gap.lean:781-798` | `gapTerm = shellDefect + ind2Term` |

## 2. 符号化推导

记 `H := leastHull(shell)`，`L := leastHull(thetaComponent)`，`V := componentVol`，`x_l := qroot^{j²}`，`s := scaleElt = incl_distinguished(qroot^{j²})`。

### 2.1 分母
`leastHull_units_smul` 给 `leastHull(s • shell) = s • H`。单位缩放：
```
V(s • H) = V(s • integral) + V(H)
         = −ord(s)·logp + V(H)
ord(s) = j²·qOrder/(2ℓ·e_w)
```

### 2.2 分子（上界）
`thetaComponent = ⋃_{φ∈indAut} φ(s • shell)`；`prop14_iii` 取 `x=qroot^{j²}` 给
```
L ⊆ a·integral，  V(a·integral)
  ≤ (−ord(s) + Σ_i d_i + 1)·logp + Σ_i [p−2<e_i](3+log e_i) + [l∈I*](3+log e_l)
```
（`d_i=differentExponent`，`e_i=ramIdx`，`I*` 为 ramified 指标集。）
由单调性 `V(L) ≤ V(a·integral)`。

### 2.3 下界
`s • shell ⊆ L`，故
```
V(L) ≥ V(s • shell) = V(s • integral)+V(shell) = −ord(s)logp + V(shell)
```

## 3. qOrder 依赖：精确相消，**有界**

把 2.1–2.3 代入 `ind2Term = V(L) − V(s•H)`：
```
下界：ind2Term ≥ V(shell) − V(H)
上界：ind2Term ≤ (Σ_i d_i+1)logp
                 + Σ_i [p−2<e_i](3+log e_i)
                 + [l∈I*](3+log e_l)
                 − V(H)
```
**`−ord(s)logp` 与上界中的 `−ord(s)` 精确相消**（这是 `leastHull_units_smul` + `componentVol_units_smul` + `prop14_iii` 的组合结果）。

因此：
- `ind2Term` **对 qOrder 有界**（O(1)），不是线性增长；
- 也**不是 frac**：`j²·qOrder/(2ℓ e)` 的 ord 只出现在被消掉的项中；`qroot` 是完整 unit，`scaleElt` 的 `j²` 指数不产生 frac 残余；
- 上界仅依赖 `d_i`（different）、`e_i`（ramification）、`p`、`V(H)` 与是否 ramified，**与 qOrder 无关**；
- 下界同样与 qOrder 无关；且 `ind2Term_nonneg` 给 ≥0。

### 3.1 对 `litLabels` / 多 label
`thetaComponent` 用 `ivLabels`（单个 distinguished label）；若换 `litLabels`（全部 label），`thetaFiniteOn` 是 `l` 的并，`prop14_iii` 的界对每个 `l` 取最大，另加 `nC` 倍；仍与 qOrder 无关。

## 4. E = gap 的增长公式候选

`gapTerm_finite`：`gapTerm(i,p,c) = shellDefect(p,c) + ind2Term(i,p,c)`；`shellDefect` 不含 qOrder（shell/不同/ramification 固定），`ind2Term` 有界。因此对固定曲线/固定 bad set：
```
E = gap = Σ_{p∈bad} Σ_{i=1..nC} [shellDefect(p) + ind2Term(i,p)] + archDefect
  = O( #bad · nC · (Σd+1)logp + ram terms + |V(H)| )
```
**E 关于 qOrder 有界**；没有 q-linear 项，也没有 frac 项。

## 5. 与 c1 数值 `Ind2` 的关系

c1 数据的 `Ind2 = Σ_j frac(j²v/(2ℓ))logp` 是**另一个（模型/归一化）量**：它把 `j²qOrder/(2ℓ)` 的整数部分丢掉，只留 frac。lana 的 `ind2Term` 不是这个 frac 和；由上面的相消，若把 c1 `Ind2` 当作 actual `ind2Term`，会错误地产生 qOrder 线性/frac 增长。
⇒ **不能把 c1 `Ind2` 直接识别为 lana `ind2Term`**；需要实际的 `componentVol/leastHull` 定义与 `V(H)` 数值。

## 6. 结论

1. `ind2Term = V(hull θComp) − V(scaleElt • hull shell)` 的 qOrder 依赖**精确相消**；
2. `ind2Term` 被 `(Σd_i+1)logp + ram terms − V(H)` 与 `V(shell)−V(H)` 夹住，**关于 qOrder 有界**；
3. `E=gap` 对固定曲线/固定 bad set 有界；`E` 的 qOrder 线性增长或 frac 增长**没有源码依据**；
4. 条件：使用 `ivLabels` 的 `thetaComponent`、`scaleEltAt = qroot^{j²}`、`leastHull_units_smul`、`componentVol_units_smul`、`prop14_iii`；`H=leastHull(shell)` 与 `d_i/e_i` 固定；`qOrder` 只通过 `ord(scaleElt)` 进入并被消掉；
5. 若 paper 的 E 出现 qOrder 线性项，它只能来自**未消掉的额外项/不同归一化**，不是这个 faithful ind2Term。

## 文件
- 本文件 `coord/FAITHFUL-E-GROWTH.md`；源码只读，无编译。