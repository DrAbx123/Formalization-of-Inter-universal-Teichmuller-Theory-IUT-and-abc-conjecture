# LOGQ-NORMALIZATION — QPilotData/logQ/lhs 是否忠实 (A1036)

| field | value |
|---|---|
| Status | **DECISION: lhs = −absLogQ 的归一化忠实（与 IUT IV Thm 1.10 的 `|log q|=(1/2ℓ)log q` 及 IUT I Example 3.2(iv) 的 q-divisor 约定一致）；iv 不稳定不是 lhs 归一化读错所致** |
| 源 | `Iut/Cor312/LeftHandSide.lean:8-93`（QPilotData, logQ, absLogQ, lhs, 文档归一化说明）；`Iut/Cor312/ThetaData/Basic.lean:171-194`（qOrder）；`Iut/Concrete/ThetaLocalConstruct/Data.lean:327-330`（ordp_qrootOf = qOrder/(2ℓ·e_w)）；`Iut/Cor312/ThetaData/AdmissiblePrime.lean:52-55`；`Iut/Implication/Invariants.lean:114`（logQAt） |

## 1. 定义（逐行）

`QPilotData`（LeftHandSide:58-67）：
```
structure QPilotData (D) where
  badFinset : Finset (FinitePlace D.F)
  badFinset_spec : ↑badFinset = badPlacesOver D.F D.E D.VBad
  weight : FinitePlace D.F -> Real            -- intended f_w/[F:Q]
  weight_pos : forall w in badFinset, 0 < weight w
```
`logQ`（:81-84）：
```
logQ := sum_{w in badFinset.attach} weight w * (qOrder w _ : Real) * Real.log (residueChar w)
```
`absLogQ`（:86-88）：`absLogQ := logQ / (2 * (D.l : Real))`；`lhs`（:90-93）：`lhs := -absLogQ`。

## 2. 文档归一化（LeftHandSide:15-31 原文）

- `log(q)` = q-divisor 的 normalized degree：坏位 w 上 `ord_w(q_w)·log p_w` 的加权和；
  `ord_w(q_w)` 是 Tate 参数的 normalized integer order（`InitialThetaData.qOrder`）；
  weights = normalized arithmetic-degree weights（intended `f_w/[F:Q]`）；
  对应 IUT I, Example 3.2(iv) 的 q-divisor 约定；
- `|log(q)| := (1/2ℓ)·log(q)`：IUT III Cor 3.12 的量，值见 IUT IV Thm 1.10 证明
  （"the quantity |log(q)| … is equal to (1/2ℓ)·log(q)"）；
- lhs = −|log(q)|。

## 3. q_v 与 qOrder 的关系（不是冲突）

- qOrder = Tate 参数 `q_Tate` 的整数阶（v_π(q)，AdmissiblePrime:52；Basic:171-194）；
- qroot（`q_v`）= `q_Tate^{1/(2ℓ)}`，其 ordp = `qOrder/(2ℓ·ramIdx e_w)`（Data:327-330）；
- 因此 **qOrder 本身是未除 2ℓ 的整数**（A1026），而 |log q| 的 1/(2ℓ) 正是把
  qroot/2ℓ 归一化补回来的因子；`logQ` 用 qOrder（整数阶）再除 2ℓ = 用 qroot 的
  ordp×e_w 的归一化一致。**不存在「应用 log(q_v) 而非 qOrder·log p」的遗漏**——
  `log q_v` 的 ordp 恰是 qOrder/(2ℓ e_w)，乘回 e_w 与权重已经包含在 q-divisor 归一化中。

## 4. 是否有另一套 logQ

- `Iut/Implication/Invariants.lean:114 noncomputable def logQAt (p : Nat) : Real`：
  按素数的分组版（`logQ = Σ_p logQAt p` 的分解形式）；
- `IdentifiedCopies:433` 用 `logQAt q / (2 * D.ℓ)`，与 `absLogQ = logQ/(2ℓ)` 一致；
- 未发现 `logQ'`、`qPilotReal`、`absLogQAlt` 等替代定义；
- `Iut/Cor312/LeftHandSide.lean` 的 docstring 是唯一归一化说明，明确引用 IUT IV Thm 1.10。

## 5. 与 paper 对照

- 仓库内的 paper 文本/摘录：`tmp/lit/Holonomy.pdf`、`tmp/lit/*.pdf`（其他 PDF 未逐一列出）；
  `coord/` 有多份 IUT 摘录（如 `coord/IUT-COMPLETION.md`、`coord/DEEP_AUDIT_ABC_IUT.md` 等）；
  **本任务未逐条比对 IUT PDF 原文**，判定以 lana docstring 对 IUT IV Thm 1.10 的引用为准；
- lana `Cor312/Statement.lean:55-59` 已注明："The intended statement may differ from the formulation
  printed in the IUT papers... the concrete inputs are the project's concretization"。

## 6. 判定

1. QPilotData/logQ/absLogQ/lhs 的定义与文档归一化**一致且忠实**：
   `lhs = −(1/2ℓ)·Σ_w weight_w·qOrder_w·log p_w`，符合 IUT IV Thm 1.10 的 `|log q|`；
2. qOrder 为整数阶、qroot 为 2ℓ-th root：两者通过 `ordp_qrootOf = qOrder/(2ℓ e_w)` 自洽，
   不存在漏乘/错除 2ℓ；
3. 未发现替代 logQ 定义；`logQAt` 是同一归一化的按素数分解；
4. 因此 **iv 不稳定不能归因于 lhs 归一化**；剩余可能：(a) rhs/theta 归一化（iv vs lit、
   Ind1 union 的处理），(b) 目标选择（concretization 偏离 paper），(c) 需要额外 q 界/正项；
5. 建议把本文件并入 A1030/A1035 的偏差证据链；最终需 owner 决策。

## 7. Lean 陈述草案

```lean
/-- logQ is the weighted sum of integer q-orders. -/
theorem logQ_eq_sum (Q : QPilotData D) :
    Q.logQ = ∑ w ∈ Q.badFinset, Q.weight w * (D.qOrder w _ : Real) * Real.log (residueChar w) := rfl

/-- absLogQ = logQ/(2l). -/
theorem absLogQ_eq (Q : QPilotData D) : Q.absLogQ = Q.logQ / (2 * (D.l : Real)) := rfl

/-- lhs = -absLogQ. -/
theorem lhs_eq (Q : QPilotData D) : Q.lhs = -Q.absLogQ := rfl

/-- qroot order is qOrder/(2l * ramIdx), consistent with the 1/(2l) normalization. -/
theorem ordp_qroot_eq (D) (v w) (h hw) :
    ordp D.Kt v (qrootOf D v) = (D.qOrder w hw : Real) / (2 * (D.l : Real) * ramIdx D.F w) :=
  ordp_qrootOf D v w h hw
```
（`logQ_eq_sum` 的 sum 记号按实际 Finset.sum 形式书写；其余为 lana 定义展开/rfl。）