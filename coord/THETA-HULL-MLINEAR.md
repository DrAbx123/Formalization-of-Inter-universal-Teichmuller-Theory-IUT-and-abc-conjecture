# THETA-HULL-MLINEAR — rhs 的 m-线性系数：sF 平均 vs literal-min (A1019)

| field | value |
|---|---|
| Status | PARTIAL (rhs 定义链已钉死：thetaHull 走 min/single-label；`-sF*A` 是 LGP 积分区域体积，不是 theta hull；qroot 阶与 m 的关系仍 GAP-QROOT) |
| 源 | IdentifiedCopies:441-456 (`logVol_lgp_integral`), ThetaRegion:124-139 (`scaleEltAt`, `qroot^{j²}`), :168-175 (`thetaFiniteOn` union over labels), :58-74 (iv/lit, min_l), Gap:909-914 (`proj_hull_thetaPilot`), Gap:747-756 (`ind2Term`) |
| 结论 | lana 的 rhs = logVol(hull(thetaPilot))，hull 由 **min_l ord_p(q_{v_l})**（literal）或单 label（iv）控制，**不是 sF 平均**；`-sF*A` 是 LGP·integralRegion 的体积（另一对象）；`dM/dm = (logp/(2l))(1 - (1/nC) sum_i j_i^2 rho_i)`，rho 为 min 阶/参考阶 |

## 1. `logVol_lgp_integral` 到底是什么

`Iut/Wall/IdentifiedCopies.lean:441-456`（GREEN）：
```
theorem logVol_lgp_integral :
    logVol D (lgp D (integralRegion D)) = -(sFactor (nC D) * D.qPilot.absLogQ)
```
文档 :441-443 明言："`log-vol(LGP·O) = -s·|log(q)|`: the theta values q^{j²}, averaged over the
capsules j = 1..l*, shift the procession-normalized log-volume by -s*|log(q)|"。
即它是 **LGP·integralRegion（体积 0 的区域）** 的 procession 平均体积，**不是**
`rhs = logVol(hull(thetaPilot))`。

## 2. thetaHull 的定义链

- `Gap:909-914` `proj_hull_thetaPilot`：hull(thetaPilot) 的 component =
  `leastHull (thetaComponent)`；
- `Gap:747-754` `ind2Term` = `V(leastHull(thetaComponent)) - V(scaleElt • leastHull(shell))`；
- `ThetaRegion:126-139` `scaleEltAt` = 在 label `l` 的 tensor factor 放 `qroot^{j²}`，
  `j = i+1`；`scaleElt` 用 `distinguished` label；
- `ThetaRegion:168-175` `thetaFiniteOn i S p c` = `union_{phi in indAut} phi ''
  (union_{l in S} scaleEltAt l • shell)`；
- `:58-66`: `ivLabels` 用 `S={j}`（单 label），`litLabels` 用 `S = S_{j+1}`（全 label）；
- `:73-74` 明文："the hull of the literal union is governed by `min_l ord_p(q_{v_l})`
  rather than the average"。

即：hull 的 q-依赖是 **min（literal）或单 label（iv）**，**不是** sF 平均；
`-sF*A` 的平均来自 LGP·integralRegion（capsule j=1..l* 的 q^{j²} 全作用），是 gap/SSIneq
链中的另一对象（`logVol_lgp_intact`-级别），不能与 rhs 混用。

## 3. dM/dm 的精确值

记 `qroot` 在 label l 的 `ordp` 为 `rho_l * m/(2l)`（定义 `rho_l := ordp(qroot_{v_l}) / (m/(2l))`，
若 `ordp qroot = m/(2l)` 则 `rho_l = 1`；qroot 定义见 `InitialThetaData.qroot`，与 `qOrder` 的
精确关系是 **GAP-QROOT**，本任务未读其定义）。

per capsule i，literal：`rhs_i^lead = -j_i^2 * min_l rho_l * m logp/(2l)`；
iv：`rhs_i^lead = -j_i^2 * rho_{j_i} * m logp/(2l)`；
procession 平均后（单 place, weight 1）：
```
rhs_lead = -(1/nC) * sum_i j_i^2 * rho_i^eff * m logp/(2l)
M_lead   = A + rhs_lead,   A = m logp/(2l)
dM/dm = (logp/(2l)) * (1 - (1/nC) * sum_i j_i^2 * rho_i^eff)
```
- 若所有 `rho_i^eff = 1`（label 同阶）⇒ `1 - (1/nC)sum j_i^2 = 1 - sF < 0`（l>=5）⇒ 平均/均匀读法
  仍是大 m 反例；此时 `logVol_lgp_integral` 的 `-sF*A` 与 theta hull 的 leading 一致（同系数）；
- 若 literal-min 使某些 `rho_i^eff < 1`，则 `dM/dm` 可能 >=0；条件（l=5, sF=2.5）：
  `sum_i j_i^2 rho_i > nC`，例如 `rho_1=1, rho_2` 小时可满足。

## 4. 判定：lana 的 RHS 是哪种

**lana 的 RHS（`rhs = processionVol thetaHull`）用 literal-min/单-label 读法，不是平均**：
- `ThetaRegion:73-74` 明确 hull 由 min_l 控制；
- `ivLabels`/`litLabels` 是两种显式读法，`concreteVariantData` 用 iv（单 label），
  `concreteVariantDataLit` 用 lit（min）；
- `-sF*A`（LGP integral region）是 gap 链的对象，不是 thetaHull 的体积。

但 `rho` 的值（qroot 阶 / m）决定 sign：若 qroot 在所有 label 上同阶（rho=1），
则**两种读法都退化为平均 sF**，大 m 反例成立（variant 对 I_n 大 n 会失效）；
若 label 阶不同，literal-min 可降低系数、使 dM/dm>=0。**GAP-QROOT 是决定性缺口**。

## 5. Lean 陈述草案

```lean
/-- Effective m-linear coefficient of rhs: -(1/nC) sum_i j_i^2 rho_i. -/
def rhsMLinearCoeff (nC : Nat) (rho : Fin nC -> Real) : Real :=
  - (1 / (nC : Real)) * ∑ i : Fin nC, ((i.1 + 1 : Real) ^ 2) * rho i

/-- dM/dm = (logp/(2l)) * (1 + rhsCoeff). -/
def dMdm (logp : Real) (l nC : Nat) (rho : Fin nC -> Real) : Real :=
  (logp / (2 * (l : Real))) * (1 + rhsMLinearCoeff nC rho)

/-- Uniform rho = 1 gives the average coefficient 1 - sF. -/
theorem dMdm_uniform (logp : Real) (l nC : Nat) (h : forall i, rho i = 1) :
    dMdm logp l nC rho = (logp/(2*(l:Real))) * (1 - sFactor nC) := by
  unfold dMdm rhsMLinearCoeff; simp [h]; ring
```
（GAP-QROOT：`rho_l` 的精确值需读 `InitialThetaData.qroot` 定义与 `ordp_qroot` 关系。）

## 6. 结论

1. `-sF*A` 是 LGP·integralRegion 体积（`logVol_lgp_integral`，GREEN），**不是** thetaHull 体积；
2. lana 的 thetaHull q-依赖 = **literal-min**（litLabels）或单 label（ivLabels），不是平均；
3. `dM/dm = (logp/(2l))(1 - (1/nC)Σ j_i² rho_i^eff)`；uniform rho=1 时 = `(1-sF)logp/(2l) <0`
   （大 m 反例）；literal-min 下可能 >=0；
4. **最终结论：取决于数据的 rho（qroot 阶）**；在 `rho=1`（同阶）退化情形下为平均、大 m 反例；
5. 决定性缺口 GAP-QROOT：需读 `InitialThetaData.qroot` 与 `ordp_qroot`，确认 `rho_l` 是否等于 1；
   这决定 variant 的 m-linear 行为，须上报 lead 决定下一步。