# IND123-GLOBAL — Ind1/2/3 的全局 label 作用与 iv 的补偿机制 (A1030)

| field | value |
|---|---|
| Status | **DECISION: lana 的 indAut 只含逐 packet 的 (Ind2) tensorAut/archIndAut，无跨 capsule/跨 label 置换；Ind1 由 thetaPilotOn 的 `S` 集合**编码（iv 只取单 label {j}）；Ind3 只是 `S ≤ hull(vcI)` 的上界；**iv 读法无 min/平均补偿 ⇒ q-不稳定的结论站得住** |
| 源 | IndAut:288-310 (`indAut := tensorAut / archIndAut`), IndAut:52-56 (`latticeAut`), :206-221 (`factorAut`/`tensorAut`), ThetaRegion:236-241 (`ivLabels={j}`, `litLabels=univ`), :271-286 (`thetaPilotOn` 逐 capsule 乘积), Ind3:122-134 (`vcI`, `vcI_le_hullOf`), Ind3:213 (`Ind3` 定义), Gap:502-545 (`gap`, `logVol_lgp_vcI_le_rhs`, `inHullOfImage_lgp`) |

## 1. indAut/Ind2 的完整分组

`IndAut:288-310`：
```
def indAut : forall (vQ) (c), Set (Tensor K vQ c -> Tensor K vQ c)
  | .finite p, c => tensorAut p c
  | .infinite, c => archIndAut c
```
- `tensorAut`（:219-221）= 逐 factor 的 `factorAut`（`g '' factorLogShell = factorLogShell`）的 tensor 积；
- `archIndAut` = 无穷位各 factor 的符号/共轭作用；
- **indAut 中没有任何跨 capsule 或跨 label 的置换**；label 类型 `Lab n i = capsule i 的 LabelType`（ThetaRegion:122）
  逐 capsule 固定；不同 capsule 的 label 类型不同，`indAut` 只在单个 tuple 的 tensor packet 上作用；
- (Ind1) 的 label 置换**不在 indAut 中**，而是通过 `thetaPilotOn S` 的集合 `S`（iv `{j}`，lit `univ`）编码；
  因此 iv 与 lit 的差别就是 S 的选择，不存在额外的全局置换群作用。

## 2. thetaPilotOn 的作用范围

`ThetaRegion:271-286`：`thetaPilotOn S` 的 region `vQ` = product over c of `thetaComponentOn i (S i) vQ c`；
- 逐 capsule i 独立；
- 无跨 capsule 的 identification（procession 平均 `(1/nC)Σ_i` 是唯一的全局操作，见 LogVolume:207）；
- 故 iv 的每个 capsule 只看见自己的 label j（= i+1），与其它 capsule 的 j' 无关。

## 3. Ind3 的作用

`Iut/Wall/Ind3.lean:213`：`def Ind3 := {S : Region D // IsAdelic D S ∧ ∀ i, S i ≤ hullOf D (vcI D) i}`；
- 即 Ind3 = 满足 `S ≤ hull(vcI)` 的 adelic regions；
- 只给**上界**，不含取 min/平均/置换的构造；
- `vcI_le_hullOf`（Ind3:132-134）、`logVol_le_logVol_hullOf`（:136-147）都是单调性上界；
- `inHullOfImage_lgp`（Gap:507-512 引用）给 `lgp·hull(vcI) ⊆ hull(Ind1-image of thetaPilot)`，
  于是 `logVol(lgp hull vcI) ≤ rhs`，即 **gap ≥ 0**；没有反向等式。

## 4. iv 读法下的 gap 化简（无全局补偿）

对 iv：`thetaHull_iv` 的 component = `leastHull(∪_φ φ(a_j • shell))`；
`a_j` 是 unit（`isUnit_scaleElt`），`leastHull` 与 unit scaling 可交换（`leastHull_units_smul`）
⇒ `leastHull(a_j • shell) = a_j • leastHull(shell)`；automorphism 部分（tensorAut）保持 shell 不改变 scaling；
因此 `V(thetaHull_iv) = V − j²·A`（逐 capsule），procession 平均：
```
rhs_iv = V − sF·A,        gap_iv = rhs_iv − logVol(lgp hull vcI)
       = (V − sF A) − (V − sF A) = 0
```
（用 `logVol_lgp`：`logVol(lgp hull vcI) = V − sF A`。）
⇒ **variant_iv ⇔ V ≥ (sF−1)A**（A1028）；V q-无关、A ∝ qOrder 无界 ⇒ 不稳定；
**Ind1/2/3 均不提供任何补偿（无跨 label 置换、无 min/平均、Ind3 只上界）**。

## 5. lit 读法对比（无全局机制时）

lit（S=univ）：逐 factor 的并集 = shell（嵌套），hull 回到 `leastHull(shell)` ⇒ `rhs_lit = V`；
`gap_lit = sF·A`（A1029）；variant_lit ⇔ `V ≥ −A`（V≥0 ⇒ 平凡真）。
⇒ 两种读法的差别完全由 S 选择决定，**不是全局 Ind1 作用的结果**。

## 6. 结论

1. lana `indAut` = 逐 packet 的 (Ind2) tensorAut/archIndAut，**无跨 capsule/跨 label 置换**；
2. (Ind1) label 置换仅通过 `thetaPilotOn S` 的 S 编码；`thetaPilotOn` 逐 capsule 乘积，无跨 capsule identification；
3. Ind3 只有 `S ≤ hull(vcI)` 的上界，无 min/平均构造；`gap ≥ 0` 来自 `inHullOfImage_lgp` 的包含关系；
4. iv：`rhs = V − sF A`、`gap = 0`、variant ⇔ `V ≥ (sF−1)A` ⇒ q-不稳定；**无补偿机制**；
5. lit：`rhs = V`、`gap = sF A`、variant 平凡真；
6. 若 paper 的 variant（IUT IV Steps (iv)-(v)，iv 读法）应为真，则 lana 的 iv 形式化与其 `rhs` 归一化必有偏差
   （候选：`rhs` 应含 Ind1 标签置换的 union、或 A 的 1/2ℓ 与 sF 的配对方式不同、或 variant 实际是 lit 的弱形式）；
   **这是形式化/paper 偏差的最终定位点**，建议上报 lead/owner 决策，不擅自改目标。

## 7. Lean 陈述草案

```lean
/-- indAut contains only per-packet (Ind2) automorphisms; no cross-capsule permutations. -/
theorem indAut_finite_eq_tensorAut (p) : indAut (.finite p) c = tensorAut p c := rfl

/-- thetaPilotOn is capsule-wise: no cross-capsule identification. -/
theorem thetaPilotOn_capsule_independent (S hS i) (vQ) (c) :
    (thetaPilotOn n S hS i).region vQ c = thetaComponentOn n i (S i) vQ c := rfl

/-- Ind3 is the upper-bound region. -/
theorem Ind3_le_hull_vcI (S : Ind3 D) : forall i, S.1 i <= hullOf D (vcI D) i := S.2.2

/-- iv variant instability (model level): V >= (sF-1)A required. -/
theorem variant_iv_iff (D) : Corollary312Variant (concreteVariantData D) <->
    logVol D (hullOf D (vcI D)) + gap D >= (sFactor (nC D) - 1) * D.qPilot.absLogQ
```

## 8. 待办

- 把本结论同步到 `coord/VARIANT-READING-DECISION.md`（补充：Ind1/2/3 无全局补偿）；
- 建议 owner 决策：target 改 lit（平凡、可证、但 ABC 桥需新证明）或 iv（需形式化/paper 偏差修复）；
- 若维持 iv：需要新的局部/全局机制（如 `rhs` 中显式含 Ind1 label union 的平均化）并证明 `V ≥ (sF−1)A`。