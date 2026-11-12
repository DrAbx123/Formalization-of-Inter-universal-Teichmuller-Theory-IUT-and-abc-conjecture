# DECOMP-ROUND2 — 第二轮：找 ∝m 正项 (A1035)

| field | value |
|---|---|
| Status | **DECISION: orderVol/PacketIndexForm/logShellRadius/shellExcess 全部 m-无关（有界）；无 +c·m logp 正项；归一化 2ℓ 位置已核（A 已含 1/2ℓ，无遗漏）；包含关系只给 rhs 下界 `V−sF·A`，不足以推 M≥0 ⇒ iv 不稳定结论维持** |
| 源 | VcI:93-105 (`orderVol = componentVol(order)`, `orderVol_nonpos`), VcI:109-113 (`−Σ differentExponent*logp ≤ orderVol`), VcI:634-640 (`PacketIndexForm = −½(d_I−d_T)logp`), VcI:462-472 (`logShellRadius`), VcI:158 (`shellExcess`), VcI:414-416 (`shellExcess_eq_tame`), VcI:601-612 (`componentVol_leastHull_tensorLogShell_eq`), IdentifiedCopies:229 (`inHullOfImage_lgp`), Gap:510-512 (`logVol_lgp_vcI_le_rhs`), IdentifiedCopies:441-456 (`logVol_lgp_integral = -sF*A`) |

## 1. orderVol 与 PacketIndexForm 的 m-依赖

- `orderVol := componentVol(order)`（VcI:93）；
- `orderVol_nonpos`（:102）：`orderVol ≤ 0`；
- 下界 `neg_sum_differentExponent_mul_log_le_orderVol`（:109-113）：
  `−(Σ_j differentExponent(w_j))·logp ≤ orderVol`；
- `PacketIndexForm`（:634-640）：Galois 情形 `mu(R_I) = −((m−1)/2)·d_w·logp`（m = tensor 因子数，非 qOrder）；
  一般情形 `mu(R_I) = −½(d_I − d_T)·logp`，`d` 是 different exponents；
- **`differentExponent` 与 `localDeg/ramIdx` 都是域扩张不变量，与 qOrder = v(q) 无关**；
  即 `orderVol` 是 m-无关的有界量（仅在 `O(Σ(3+log e))` 内）。

## 2. logShellRadius(scaled) 与 shellExcess

- 未缩放：`componentVol(leastHull(tensorLogShell)) = Σ_j logShellRadius(w_j)·logp`（VcI:601-612）；
  `logShellRadius = sSup(−ordp)`（:462-465），是 shell 的几何量，**与 q 无关**；
- 缩放 `a = qroot^{j²}`（unit of Total）：`componentVol(a • leastHull(shell)) = componentVol(a • O) + componentVol(leastHull(shell))`
  （`componentVol_units_smul`），其中 `componentVol(a • O) = −ord(a)·logp = −j²·qOrder·logp/(2ℓ·e_w)`；
- `shellExcess`（:158）：`μ(leastHull shell) − μ(shell)`；tame 公式 `= Σ(1−1/e_j)logp`（:414-416），**m-无关**；
- **半径随缩放减少 k 的效应已包含在 `−ord(a)logp` 中（线性负），没有符号反转；shellExcess 无 −x 项的符号反转**。

## 3. 归一化 2ℓ 因子核对

- `A = Σ_w weight_w·qOrder_w·logp_w/(2ℓ)`（LeftHandSide:81-88）；
- `scaleElt` 的 ordp = `j²·qOrder/(2ℓ·e_w)`（Data:327-330 的 qroot 阶 × j²）；
- `logVol_lgp_integral = −sF·A`（IdentifiedCopies:444-456）：`sF` 与 `A` 直接配对，**没有额外 2ℓ**；
- 故 rhs 的体积线性项 = `−(1/nC)Σ_i j_i²·qOrder·logp/(2ℓ) = −sF·A`；不存在「该乘 2ℓ」的未归一化因子。

## 4. 包含关系路线

- `inHullOfImage_lgp (S : Ind3 D) : InHullOfImage D (lgp D S.1)`（IdentifiedCopies:229）；
- `Gap:507-512 logVol_lgp_vcI_le_rhs`：`logVol(lgp·hull(vcI)) ≤ rhs`，即 **`V − sF·A ≤ rhs`**；
- variant 需要 `rhs ≥ −A`；结合只差 `V − sF·A ≥ −A ⇔ V ≥ (sF−1)·A`——正是 iv 不稳定条件，
  包含关系本身**不能提供**（它是下界 `V−sF A`，比 `−A` 更小，方向不利）；
- 反向包含（theta hull ⊆ 某 q-pilot log-shell）在 lana 中不存在：`hull(theta)` 通常**大于** `lgp hull(vcI)`，
  故 `R ≤ A` 不能由包含关系得到。

## 5. 其他候选与判定

| 候选 | m-依赖 | 结论 |
|---|---|---|
| orderVol | 无（≥ −Σ differentExponent·logp） | 不能抵消 |
| PacketIndexForm | 无（d_I,d_T, ≠ qOrder） | 不能抵消 |
| logShellRadius(scaled) | 线性负 `−j²A`（不是正） | 增加负项 |
| shellExcess | 无（tame `Σ(1−1/e)logp`） | 不能抵消 |
| archDefect | 无（常数） | 不能抵消 |
| ind2 | frac/有界（A1022）或 lit 线性（A1027） | iv 下为 0 |
⇒ **lana 源中不存在 ∝m 正项**；iv 的线性负项无法抵消。

## 6. Lean 陈述草案

```lean
/-- orderVol is m-independent: bounded below by differentExponent only. -/
theorem orderVol_bounded_below (hc : forall j, IsOver K p (c j)) :
    -(∑ j, differentExponent K (finPart K (c j))) * Real.log p <= orderVol p c :=
  neg_sum_differentExponent_mul_log_le_orderVol hc

/-- Hull inclusion gives the lower bound rhs >= V - sF*A. -/
theorem rhs_ge_V_sub_sF_mul_A (D : InitialThetaData) :
    logVol D (hullOf D (vcI D)) - sFactor (nC D) * D.qPilot.absLogQ <=
      (concreteVariantData D).rhsData.rhs :=
  logVol_lgp_vcI_le_rhs D

/-- iv variant needs V >= (sF-1)*A (same condition, no new positivity). -/
theorem variant_iv_iff (D : InitialThetaData) :
    Corollary312Variant (concreteVariantData D) <->
      (sFactor (nC D) - 1) * D.qPilot.absLogQ <= logVol D (hullOf D (vcI D)) + gap D := by
  rw [corollary312Variant_iff, variant_iff_le_rhs]
  have h := gap_eq_rhs_add D
  linarith
```

## 7. 结论

1. `orderVol`/`PacketIndexForm`/`logShellRadius`/`shellExcess` 都 m-无关或有界；**无 ∝m 正项**；
2. scaled logShellRadius 只有线性**负** `−j²A`（半径减少 k 已含在该项，无符号反转）；
3. 2ℓ 归一化已核对：A 含 1/(2ℓ)，rhs 线性项 = −sF·A，无遗漏因子；
4. 包含关系 `lgp hull(vcI) ⊆ hull(theta)` 只给 `rhs ≥ V − sF A`（比 −A 更小），不能推 `M≥0`；
   反向包含不存在 ⇒ `R ≤ A` 路线不可行；
5. 综上：**iv 的 q-不稳定是 lana 源中的真实性质**（在其形式化陈述下）；需要 owner 决策（改 lit 目标 / 修 rhs 归一化 / 引入 UB 条件）；
6. 建议把本文件与 A1030/A1028 合并上报，作为「形式化-论文偏差」的最终证据链。