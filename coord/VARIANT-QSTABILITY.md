# VARIANT-QSTABILITY — variant 是否 q-缩放稳定？(A1025)

| field | value |
|---|---|
| Status | **DECISION: 链 M = V + gap − (sF−1)A 忠实于 lana 源；V q-无关（已证源）；gap 为 hull 扩大（A1022 frac/有界）；⇒ 若 gap 有界，lana 的 variant/SSIneq 在本文形式化中 NOT q-缩放稳定** |
| 源 | Ind3:57-62 (`vcIComp` = 纯 shell/logShell), VcI:734-744 (`logVol_hull_vcI_eq`), Gap:502-550 (`gap`, `gap_eq_rhs_add`, `ss_iff_le_rhs_sub_gap`, `variant_iff_le_rhs`), IdentifiedCopies:281 (`logVol_lgp`), Gap:594-599 (`lgpComp = scaleElt • shell`), IdentifiedCopies:441-456 (`logVol_lgp_integral`) |

## 1. 三环逐一核对

### 环 1: V 的 q-无关性 —— 忠实（源级确认）
`Iut/Wall/Ind3.lean:57-62` `vcIComp`：
```
| .finite p, c => LocalTheory.shell ...        -- 纯 log-shell，无 theta/q
| .infinite, c => LocalTheory.logShell ...     -- 无穷位 log-shell
```
`vHull` 的 `logVol_hull_vcI_eq`（VcI:734-744）= `(sum_i sum_v hullPacket_i v)/nC`，
hull 只作用于 log-shell。⇒ **V = logVol(hull(vcI)) 与 qOrder 无关**（源级确认）。

### 环 2: gap = rhs − (V − sF·A) —— 忠实（Gap 定义链）
- `gap D := rhs − logVol(lgp·hull(vcI))`（Gap:502-505）；
- `gap_eq_rhs_add`（Gap:521-527）：`gap = rhs + sF*absLogQ − V`（用 `logVol_lgp` + `logVol_lgp_integral`）；
- `IdentifiedCopies:281 logVol_lgp`：`logVol(lgp S) = logVol S − sF*absLogQ`（adelic S）；
- 故 `rhs = V + gap − sF*A`；variant（`variant_iff_le_rhs`，Gap:536-540）：`−A ≤ rhs`
  ⇔ **`V + gap ≥ (sF−1)A`** ✓ 与 lead 的链 M = V + gap − (sF−1)A 完全一致。

### 环 3: rhs 的 q-依赖 —— 全在 gap
`rhs = V + gap − sF A`；V q-无关，`sF A` 已知线性；故 rhs 的 q-依赖 = **gap 的 q-依赖**。
`gap = packetVol(thetaHull) − packetVol(lgp·hull(vcI))`：两者都含 `scaleElt`（`lgpComp` Gap:594-599
`= scaleElt • shell`；`thetaComponent` ThetaRegion:168-175 也是 `scaleEltAt_l • shell` 的 union），
故 q 的**共同缩放部分相消**，gap 只剩：hull/automorphism 扩大差 + rounding（ind2 型）
⇒ 依 A1022 为 **frac/有界**（`≤ Σ(3+log e)` 级），**不是 ∝ m**（若这一条成立）。

## 2. 判定：variant 是否 q-缩放稳定

若 gap 有界（A1022 + VcI:313-319 的 `|shellDefect+orderVol| ≤ Σ(3+log e)`），则
```
V + gap − (sF−1)A = (q-independent) + (bounded) − (sF−1)*(m logp/(2l))
  → −∞   as m = qOrder → ∞   (sF−1 > 0, l >= 5)
```
⇒ **lana 的 variant（以及 SSIneq，因为 variant 是其较弱形式）在本文形式化中不是 q-缩放稳定的**；
对固定曲线族取 qOrder = n 任意大（11a1 I5, 858k2 I21, 9546f3 I72）且 l ∤ n（admissible），
variant 将失效，除非 gap 实际含 ∝ m 的正项。

## 3. 哪个环节可能不忠实（三种可能，按概率）

1. **gap 可能含 ∝ m 项（最可能）**：`thetaHull` 的 hull 对 contracted scaled shells 的扩大
   可能随缩放幅度线性增长（`ind2` 的 frac 结论只覆盖 `leastHull` 的局部差，不覆盖整个
   `hullOf thetaPilot` 的 Ind1/Ind3 扩大）。若 gap 含 `+c*m` 项，则 M 可稳定；
   **GAP-GAP-MLINEAR**：需精确算 `gapHullAt` 的 m-线性系数（A1017 的 QORDER-SIGN 与 A1022 的
   frac 结论只算了 ind2 局部，不是整个 gap）。
2. **rhs 归一化可能读错**：`rhs = R.vol.processionVol R.thetaHull`，而 `concreteVariantData`
   的 `thetaPilot` 可能是 `lgp·hull(vcI)` 本身（则 gap=0）或含额外 Ind1 选择；
   Gap:507-512 用 `inHullOfImage_lgp` 只给 **≤**，未说等号；若 `thetaPilot` 定义不同，
   `rhs` 的归一化可能不是 `V + gap − sF A`。
3. **A 的 qOrder 无界但 variant 定义可能只对特定 D（bad 集有限/高度有界）**：
   `AdmissiblePrime` 只要求 l ∤ qOrder；没有高度界。若 paper 的 variant 实际范围含高度界，
   则形式化陈述需补该界。

## 4. Lean 陈述修正建议

```lean
/-- Algebraic form of the variant chain (Gap:502-550). -/
theorem variant_iff_decomp (D : InitialThetaData) :
    Corollary312Variant (concreteVariantData D) <->
      (sFactor (nC D) - 1) * D.qPilot.absLogQ <= logVol D (hullOf D (vcI D)) + gap D := by
  rw [variant_iff_le_rhs]
  have h := gap_eq_rhs_add D
  linarith

/-- If gap is bounded and A is large, the variant fails (q-instability). -/
theorem not_variant_of_large_q (D : InitialThetaData) (G : Real)
    (hgap : gap D <= G)
    (hlarge : logVol D (hullOf D (vcI D)) + G < (sFactor (nC D) - 1) * D.qPilot.absLogQ) :
    ¬ Corollary312Variant (concreteVariantData D) := by
  rw [variant_iff_decomp]
  intro h
  linarith
```
并新增**显式有界 q 版本**作为论文口径候选：
```lean
def VariantBoundedQ (B : Nat) : Prop :=
  forall (D : InitialThetaData), (forall w hw, D.qOrder w hw <= B) ->
    Corollary312Variant (concreteVariantData D)
```
（若 paper 的 variant 实际需要 q 有界/高度界，应写这个版本；否则形式化与 paper 不符。）

## 5. 结论

1. `V` q-无关：**忠实**（Ind3 源级确认）；
2. `gap = rhs + sF A − V`：**忠实**（Gap:502-550 链）；
3. 故 `variant ⇔ V + gap ≥ (sF−1)A`；若 gap 有界（A1022 的 ind2 结论）⇒ **variant 不是 q-缩放稳定的**，
   大 m 必然失效；
4. 唯一救活可能 = **gap 含 ∝ m 正项**（GAP-GAP-MLINEAR，需算整个 gapHullAt 的 m-系数，
   而非仅 ind2 局部）；其次是 rhs 归一化读错；
5. 建议：先补 GAP-GAP-MLINEAR（`gap` 的精确 m-展开）；若 gap 有界，则形式化 variant 需
   加 `qOrder ≤ B` 或高度界，并明确其与 paper 的偏差；
6. 本文件不修改 Lean 生产文件；`Mzk1MDecompositionActual` 的 GAP-IND2 应同步为
   「ind2 frac/有界；但 gap 的整体 m-系数待算（GAP-GAP-MLINEAR）」。