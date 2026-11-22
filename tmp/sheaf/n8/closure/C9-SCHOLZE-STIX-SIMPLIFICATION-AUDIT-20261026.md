# Scholze–Stix 简化模型攻击审计

日期：2026-10-26。目标：攻击批评者把简化模型的矛盾直接升级为完整 IUT 反例的逻辑，不替 IUT source theorem 宣布已证。

## 判定

当前可以严格反驳的是以下过强推理：在一个共同的 ordered carrier 中，把 q-pilot 与 Theta-pilot 当成同一个点，把 hull 压在两者之间，并把两者读数强制放进同一个单值实线；若再有 `theta = factor * q`、`factor > 1`、`q < 0`，则模型矛盾。这个矛盾来自额外同一化和 tightness 前提，不能直接反驳完整 IUT。

当前不能据此声称 Scholze–Stix 的完整论证已经被击破：他们的文本还讨论了多个 abstract/concrete `R` 空间、集合值 indeterminacy assignment 和“blurring”。因此剩余争点是他们的简化是否保持了足够的 source content，而不是简单的 `q != theta` 算术。

## Lean 证据

试验文件：`tmp/sheaf/n8/closure/C9-SCHOLZE-STIX-SIMPLIFICATION.lean`。

已通过：

```text
lake env lean tmp/sheaf/n8/closure/C9-SCHOLZE-STIX-SIMPLIFICATION.lean
exit 0; stdout/stderr empty; no sorry/axiom
```

文件中的 `TightCriticData` 明确把批评模型的额外前提拆开：

- 一个共同 `PartialOrder` 和单一 `vol : Omega -> Real`；
- `qPilot = thetaPilot`；
- `qPilot <= hull <= thetaPilot` 的 tight-hull 链；
- 单值读数 `q_read`、`theta_read`、`hull_read`；
- `q < 0`、`factor > 1`、`theta = factor*q`。

`tight_critic_collapse` 证明这些前提推出 `False`。`SlackPilotData` 的具体 witness 取 `q=-1`、`theta=-2`、`hull=-1`、`factor=2`，保留 `q <= hull` 和 scalar law，但去掉 q/Theta endpoint equality 与 `hull <= theta`；该模型一致。这证明：

```text
tight same-space critic model contradiction
  ≠ contradiction in every ordered/readout model
```

这不是完整 IUT counterexample，也不是 IUT proof；它只精确证明简化推理的适用边界。

## 原文差异

Scholze–Stix 自己在其文本 [§2.1](/D:/lean/vendor/promachina/snapshots/1fa6387f11fb6dc67eb618b8138e6bc64f56b039/docs/scholze-stix-why-abc-is-still-a-conjecture.md:225) 明说采用 radical simplifications，包括沿 identity 识别对象和把 Hodge theater 简化为抽象同构曲线。其关键图在 [§2.2](/D:/lean/vendor/promachina/snapshots/1fa6387f11fb6dc67eb618b8138e6bc64f56b039/docs/scholze-stix-why-abc-is-still-a-conjecture.md:609) 中把 abstract pilot、concrete pilot 和标准 `R` 的识别放在一起，并据此讨论 `j^2` 缩放与 monodromy。

IUT III 的 toy model 不是无条件擦除标签：

- `atoy` 明确使用两个带 `q`/`Theta` 标签的不同 `R` 副本；
- 抽象符号 `*` 先与两个副本没有先验关系；
- `dtoy` 把 indeterminacy 写成集合值半直线 `R_{<= -2h+epsilon}`；
- `etoy` 的关键前提是：需要先验证这个集合值 assignment 能从 q-side underlying structure 内在构造，且不破坏 q-side 条件。

证据：`IUT-III.txt:11027-11114`。因此从 `q != theta` 得到 source 不可能，至少还需要把 source assignment 强化为单值 selector、逐点 concrete lifts、严格交换图、非零读数以及禁止 blur/quotient。

## j^2 争点的精确范围

在共同实数坐标、共同 reference、共同 `M`、且把第 `j` 个 concrete Theta degree 直接当成 `j^2 Q` 的前提下，均匀平均确实是

```text
mean_j(theta_j) = (mean_j j^2) * Q,
mean_j j^2 = ell*(ell+1)/12  for ell odd.
```

共同 `det^M`、Ob3 的权重和 `O(-)` 修正并不自动等于逐标签的 `1/j^2` 缩放。若 source 的“suitably normalized with respect to j”给出实际的 `rho_j`，必须逐项证明 `sum w_j*rho_j*j^2 = 1` 以及它与 Kummer/procession maps 相容。仅有 `M` 或“取平均”不够。

因此我们已经击破的是“raw j^2 average 自动变成 q-readout”的简化推理；还没有决定完整 IUT 的 source `j`-normalization 是否提供所需补偿。

## 三层验收

| 层级 | 当前结果 |
|---|---|
| 简化模型 | `tight_critic_collapse` 已编译；额外同一化导致矛盾 |
| source assertion | IUT toy model 明确保留标签/集合值 assignment；`etoy/fitw` 是 source-level construction assertion，未独立展开 |
| 完整 IUT 反例 | 未构造 source-compatible complete `C` 或严格失败 readout；不能宣称 IUT 被反驳 |

最终结论：**批评者的 tight point-identification 模型不能直接代表 IUT，因此由该模型得出的矛盾不能直接攻击 IUT；但批评者对 abstract-to-concrete degree map、`j^2` normalization 和 source assignment 的质疑仍未被完整 source construction 消除。** 这是一项有效的模型层反驳，不是完整 IUT 的正面证明。

`statement_compiles`: Lean 诊断 exit 0；`proof_body_checked`: 试验文件已检查；`kernel_closed`: 仅该诊断文件；`target_accepted`: 完整 IUT false。

## 2026-10-26 premise-necessity addendum

Two scalar routes have now been separated and checked in C9-SCHOLZE-STIX-SIMPLIFICATION.lean:
- Endpoint route: common carrier/readout, same pilot point, theta = factor*q, and factor != 1 imply q=0. No order, hull, monotonicity, or sign premise is used. q<0 is sufficient for contradiction; q!=0 is the exact obstruction. Zero and drop-one witnesses remove pilot identification, common-readout compatibility, nontrivial factor, or scalar law.
- Tight-hull route: q<0, factor>1, theta=factor*q and q<=H<=theta in one ordered real carrier are contradictory; pilot-point equality is absent. For factor>1, there exists H with q<=H<=factor*q iff q>=0. Drop-one witnesses remove either bound, sign, factor inequality or scalar law.
- Toy-ray membership is exactly -h in {x | x<=-2h+eps} iff h<=eps. This lemma supplies no source estimate on eps.
- Lead verification from D:/lean: lake env lean tmp/sheaf/n8/closure/C9-SCHOLZE-STIX-SIMPLIFICATION.lean exited 0 with empty stdout/stderr; grep found no sorry/axiom. These are scalar-model results, not an IUT source construction or a proof about every part of Scholze-Stix's argument. Source normalization/assignment remains separate.