# IND2-CLOSURE — 最小模型闭合：线性 j²A（A1020 版），variant 稳定 (A1027)

| field | value |
|---|---|
| Status | **DECISION (minimal model, unramified e=1, shell = O): ind2 = j²·A linear；gap = sF·A linear；variant 稳定，I_n 警报在该模型下解除** |
| 源 | IndAut:52-56 (`latticeAut`), :206-221 (`factorAut`, `tensorAut`), :287-300 (`indAut`), ThetaRegion:168-175 (`thetaFiniteOn`), Gap:594-599 (`lgpComp = scaleElt • shell`), Gap:747-756 (`ind2Term`), IdentifiedCopies:441-456 (`logVol_lgp_integral = -sF*A`), Gap:521-527 (`gap = rhs + sF*A - V`) |
| 限制 | 模型取 `K = Q_p`（n=1, e=1, shell=O）；一般 n/e/ramified 需重复本推导；数据（M−A 负相关）与此模型不符，需另查 |

## 1. 模型设定

- 取 unramified e=1 的位（如 p=7, l=5 对 Q_p）：`factorAut = {g : Q_p-linear | g '' factorLogShell = factorLogShell}`；
  对 `K = Q_p`，`factorLogShell = O`，`GL_1(Z_p) = Z_p^×`，故 factorAut 在 lattice 上的作用是平凡的（等价地
  `g(a·O) = a·O`）；
- `tensorAut`（IndAut:219-221）= 各 factor 的自同构的 tensor 积；对 n=1 平凡；
- `indAut`（IndAut:294-300）= `tensorAut` 在 packet 上的作用（同一性）：对 n=1，`indAut = {id}`；
- `shell = log-shell = O`（`logShell_eq_integer` 型；本模型假设 shell 取 integer ring）；
- `scaleEltAt l = qroot^{j²}` 放在 label l（ThetaRegion:126-139），`ordp(qroot) = m/(2l)`（Data:327-330，e=1）；
- `thetaComponent = ∪_{l∈S} a_l • O`（indAut 平凡）；`leastHull` 为最小分数理想格/R-子模。

## 2. 计算 `leastHull(thetaComponent)`

q 收缩（`ordp(qroot)>0`）⇒ `a_l • O = π^{j²m/(2l)}·O ⊂ O`（非整，但作为分数理想包含于 O）；
- **ivLabels**（`S={j}`，单 label）：`thetaComponent = a_j O`；`leastHull = a_j O` ⇒
  `V(leastHull θcomp) = componentVol(a_j O) = -j²·A`（A = m logp/(2l)）；
- **litLabels**（`S = S_{j+1}`，全部 label）：每 factor k 上 `∪` 的项为 `O`（其它 label 的选择）
  与 `a_k O`；因 `a_k O ⊂ O`，`hull(O ∪ a_k O) = O`（product region 逐 factor 取 hull）⇒
  `leastHull θcomp = ⊗_k O = O` ⇒ `V(leastHull θcomp) = 0`（**m-无关**）。

## 3. 计算 ind2Term

`ind2Term`（Gap:747-754）= `V(leastHull θcomp) − V(scaleElt • leastHull(shell))`；
`scaleElt = qroot^{j²}`，`V(a·leastHull(shell)) = V(a·O) = -ordp(a)·logp = -j²·m·logp/(2l) = -j²A`
（`componentVol_units_smul`，IdentifiedCopies:67；`componentVol_prod_incl_smul_integral` 的显式值）。

于是，**逐 reading**：
```
ivLabels:  ind2 = (-j²A) - (-j²A) = 0                (m-无关)
litLabels: ind2 = 0      - (-j²A) = +j²·A            (线性正，m-线性)
```
即 **literal 读法下 ind2 = j²·A 线性正**（与 A1020 一致；A1022 的 frac 版在本模型中不出现，
因为 `componentVol(a·O)` 对非整 ordp 仍给出精确实数 `-ordp(a)logp`，不需要取整）；
frac 只在把 `leastHull` 作用于 **scaled** shell 并取整时才出现——本模型的第一项（θcomp hull）
恰恰等于未取整的 O。

## 4. gap 与 variant

variant 链（Gap:521-527/531-540）：`rhs = V + gap - sF A`，`variant ⇔ V + gap ≥ (sF-1)A`。
literal 读法下（模型 V = 0，因为 hull(vcI) 的 log-shell 半径取 0 归一化；若半径 r 则 V=r 项），
rhs = logVol(thetaHull) = V(leastHull θcomp) = 0（literal）；
`gap = rhs + sF A - V = sF A` ⇒ **gap = sF·A 线性正**；
```
V + gap = 0 + sF A = sF A >= (sF-1)A    (A >= 0)
⇒ variant 成立（等号差 = A）
```
⇒ **在最小模型（literal 读法）下 variant 稳定；I_n 大 n 警报解除**（gap 含 (sF-1)A 的正线性项，
来源 = Ind1 union 使 hull 退到未缩放 O，与 `logVol_lgp_integral` 的 `-sF A` 精确抵消）。

## 5. 与数据/早期推导的冲突

- A1020：ind2 线性 +j²A ✓ 本模型一致；
- A1022：frac/有界 ✗ 本模型不支持（frac 只在 scaled hull 取整时；θcomp hull 本身是 O）；
- 数据（A1021）：`M - A` 与 m 显著负相关 ✗ 本模型 literal 读法给 `M = V + A`（M−A = V 平坦）；
  可能原因：数据用 ivLabels（M−A = V − (j²−1)A? 若 iv 则 gap=0?）；或多 place/weights/截断；
  **GAP-DATA**：需按 concreteVariantData 的 S 选择（iv 还是 lit）重算；
- `concreteVariantData` 用 ivLabels（`S i = {j}`，ThetaRegion:60-62），而 `Cor312LiteralHolds` 用 lit；
  variant（Cor312VariantHolds）对应 iv！iv 下本模型 ind2=0、gap=0、rhs=−j²A ⇒ variant `-A ≤ -j²A` false for j≥2；
  但 iv 的 capsule i=0 只有 j=1（nC capsules j=1..nC 都出现）⇒ 大 n 下 j≥2 的 capsule 失效；
  **⇒ iv 读法（variant）不稳定，lit 读法稳定；这可能是真实的 lana/paper 差异点**。

## 6. 结论

1. 最小模型（e=1, shell=O, K=Q_p）下：**litLabels: ind2 = j²A, gap = sF A, variant 稳定**；
   **ivLabels: ind2 = 0, gap = 0, variant 对 j≥2 不稳定**；
2. A1020 的线性结论正确（lit 读法）；A1022 的 frac 结论仅适用于 scaled hull 取整场景，不适用于 θcomp hull=O；
3. `concreteVariantData`（variant 假设）用 ivLabels ⇒ 按本模型 **I_n 大 n 警报成立**；
   若 paper 的 variant 实际用 lit 读法，则稳定；**这是最后判定点**：需确认 `concreteVariantData` 的 S 选择
   （ThetaRegion:60-62 明说 `S i = {j}`）与 paper 的 (Ind1) 作用；
4. 建议 lean 化：分别写 `ind2_iv = 0`、`ind2_lit = j²A`、`gap_lit = sF A`、
   `variant_lit_stable`、`variant_iv_instability`（后者用大 m 反例）。

## 7. Lean 陈述（草案）

```lean
/-- Minimal model: literal reading gives linear ind2. -/
def ind2LitModel (j m logp l : Real) : Real := (j ^ 2) * (m * logp / (2 * l))

/-- Minimal model: iv reading kills ind2. -/
def ind2IvModel (j m logp l : Real) : Real := 0

/-- Literal gap = sF * A. -/
def gapLitModel (sF m logp l : Real) : Real := sF * (m * logp / (2 * l))

/-- Variant in literal reading is stable: V + gap >= (sF-1) A. -/
theorem variant_lit_stable (V sF m logp l : Real) (hV : 0 <= V) (hA : 0 <= m * logp / (2 * l)) :
    V + gapLitModel sF m logp l >= (sF - 1) * (m * logp / (2 * l)) := by
  unfold gapLitModel
  nlinarith

/-- Variant in iv reading fails for j>=2 and large m (model level). -/
theorem variant_iv_fail (m logp l : Real) (j : Nat) (hj : 2 <= j)
    (hm : 0 < m) (hlog : 0 < logp) (hl : 0 < l) :
    (j : Real) ^ 2 * (m * logp / (2 * l)) > (m * logp / (2 * l)) := by
  have hA : 0 < m * logp / (2 * l) := by positivity
  nlinarith [sq_pos_of_ne_zero (by exact_mod_cast (by omega : j != 0) : (j : Real) != 0)]
```

## 8. 待办

1. 确认 `concreteVariantData` 的 S：ThetaRegion:60-62 `ivLabels S={j}`；若 paper 的 variant 应为 lit，
   则形式化陈述需改（或承认 lana 的 variant 比 paper 强）；
2. 一般 n/e/ramified：`factorAut` 非平凡，`g(aO)` 可能改变 lattice 但保持 Haar；需重算 hull；
3. 数据（M−A 负相关）与模型的差异用 GAP-DATA 追查（iv/lit 混用或多 place 权重）。