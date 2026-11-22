# C9 固定-C 路线去重审计与乘子规范化

日期：2026-10-26。范围：U2/K2 末次 evaluation、splitting generator、cQ3 局部结构态射与 q-readout。目的：停止重复重写，保留一份可复用的公式入口，并明确真正尚未构造的 source constructor。

## 结论

本轮没有发现新的 fixed-C source constructor。前几天的工作已经覆盖：

1. Remark 3.10.2 的交换方形把 IPL 复合约化为 `U2 K2`；这只运输已经给定的 q-pilot 标记同构类。
2. cQ3 给出带到 hull determinant 的 structure-poly-morphism 的局部对象、global realified 对象和 localization isomorphism；它不按定义给出实际 final-evaluation 输出族中的 q-mark，也不自动产生 q-to-hull 的 global map。
3. 共同 `M`、`O(-)` reference、place/label weights 和 signed readout 下，若实际比较乘子已经给出，则局部除子账本为 `h-Q=S-kappa`，更一般的 tensor degree 为 `h-dQ=S-kappa`。但当前没有从固定 admissible `C` 构造这些乘子及其 global descent。
4. 唯一保留的活动叶是 fixed-C 的 `FinalEvaluationQMark` / `XiEToXiFOutputReadoutProjection(C)`；A1/A2/A3 重证、数值分支、抽象 sheaf 和 `OriginalInput -> Input` 都不再重复。

## 重复簇归并

| 已有记录簇 | 已经解决/排除的内容 | canonical 入口 |
|---|---|---|
| 10-24 `C9-LOCAL-GLOBAL-DESCENT-ATTACK`、`C9-MARKED-IMAGE-DESCENT` | cQ3 collection 不会凭对象清单自动给全局态射；已有局部比较的账本为 `h-Q=S-kappa` | 两个文件的 local-global guard |
| 10-25 `C9-C1-LOCAL/IND/DET/IPL/LOOP/APT` 与 `REVIEW-COR312-*` | log-volume 加性、Ind1/2/3、det、IPL、closed loop、APT/SHE 均不能单独推出 q-output membership；早期 exact-membership 推导已撤回 | `C9-FINALEVALUATIONQMARK-DEPENDENCY-AUDIT-20261026.md` |
| 10-25 `C9-C1-FULL-TH310-BASIS` | various further rigidifications 不等于固定 q 必在受限输出子集；保留为历史纠正 | `C9-C1-HANDOFF-SUMMARY-20261026.md` |
| 10-26 `C9-CARRIER-ONE-SIDED-REUSE`、`C9-HULL-CARRIER-*`、`C9-C1-MARKED-GATE-RECHECK`、`C9-C1-SINGLE-AGENT-NATURAL-PATH` | IQ/O carrier、hull、det^M、reference、readout 的条件比较已写完；缺的是 marked landing / actual family provenance | `C9-HULL-CARRIER-SHEAF-DESCENT-20261026.md` |
| 10-26 `C9-XIE-*` | xi-e fixed-q 可执行性与 xi-f output-readout projection 已分层；接受 xi-e/xi-f 才能条件闭合标量步骤 | `C9-XIE-SOURCE-CONDITION-AUDIT-20261026.md` |
| 10-26 `C9-U2K2-SQ3-MARKED-TRACE` | `U2 K2` 约化和条件类型方形已写；未实例化 fixed-C localization maps/cocycle，也未构造 q-mark 到 sQ3 output 的箭头 | 本文件的公式与该 trace §§6–7 |

这些簇之间是同一 source gap 的不同投影，不应再各自启动一次自然语言证明。

## 只保留这一套比较乘子公式

固定一份 admissible `C`。令 `Phi = U2 K2`，在相干的 full-poly-isomorphism 代表下写 `eta_prime_v = Phi_v(eta_q,v)`。这一步只给 q-side 的 transported mark。若有 q-side transitions `t_ij`，给定相容分量时 `t_prime_ij = Phi_j t_ij Phi_i^{-1}` 并继承 cocycle；它没有 `det^M(H_C)` 作为陪域。

cQ3 的类型正确写法是：`real_v : L_v -> real_v(L_v)`、`Loc_v : G -> Loc_v(G)`、`lambda_v : real_v(L_v) ≅ Loc_v(G)`、`mu_v : real_v(H_v) ≅ Loc_v(H_global)`。候选局部态射 `u_v : L_v -> H_v` 与全局态射 `g : G -> H_global` 必须满足

`mu_v ∘ real_v(u_v) = Loc_v(g) ∘ lambda_v`.

直接写 `G -> L_v` 或把 cQ3 的 `lambda_v` 冒充成未核实的 `rho_v` 都会丢失域/陪域。这个方形是兼容性条件，不是现有 source constructor。

在固定 frames `e^q_v ∈ L_v`、`e^H_v ∈ H_v` 下，若选择 cQ3 允许的 linear representative `u_v`，定义 `u_v(e^q_v) = c_v e^H_v`。若两端嵌入同一个 local field/fractional-ideal carrier，真正作用在 ambient elements 上的比较乘子 `m_v` 满足 `u_v(x)=m_v x`，所以

`c_v = m_v e^q_v / e^H_v`,  即  `m_v = c_v e^H_v / e^q_v`.

`c_v` 是换框后的坐标，不能直接当作 `m_v`。换 frames 会改变 `c_v`；cQ3 只给 `Aut(det^M(H_v))`-orbit，通常不给 canonical representative。torsion/root-of-unity 的 realified contribution 为零；一般 unit 只有在来自相容 global unit/gluing 时才可用 product formula 消去。

若局部 vector-map 是 `T_v`，先取各 direct summand 的 weight-compatible determinant，再取共同的 `M` 次 tensor，并同时带上 `O(-)` inverse-reference correction。`M`、reference 和 weights 必须来自同一 `C`；不能为填数值 gap 另选。

## 乘子对读数的影响

在相同 reference 下，记 input line 与 target determinant line 的局部 divisor/exponent 为 `alpha_v`、`beta_v`，有效余量为 `Z_v >= 0`。若实际比较是 degree `d` 的有效 morphism，局部式为

`d alpha_v + Z_v = beta_v + div_v(m_v)`.

取原 procession weights 和 degree normalization 后，记 `A=(div_v(m_v))_v`、`kappa=deg(A)`、`S=deg(Z)`，得到

`d Q + S = h + kappa`,  从而  `h - d Q = S - kappa`.

线性情形 `d=1` 才是 `h-Q=S-kappa`。有限 place 若 `m_v = pi_v^{n_v} u_v`，其中 `u_v` 为 unit，则按 Prop. 3.9 的符号约定局部 readout shift 为 `Delta_v = - n_v log N(v)`；无穷 place 按原 normalization 加入 `d_v log |m_v|_v`。全局加权和等于 arithmetic degree。若所有 `m_v` 真来自同一个 global realified rational/function multiplier，product formula 给 `kappa=0`；只有 local multipliers 时 `kappa` 不受控。合法的 source 交付是实际证明 `S >= kappa`，或给出真实 signed-epsilon/output witness；不能把 `kappa=0` 作为新增假设。

公式证据入口：IUT-III.txt:6738–6770、6832–6856、7788–7868、8264–8322；`C9-LOCAL-GLOBAL-DESCENT-ATTACK-20261024.md`；`C9-CARRIER-ONE-SIDED-REUSE-20261026.md`；`C9-U2K2-SQ3-MARKED-TRACE-20261026.md` §§7.1–7.2。它们是条件计算规则，不是 fixed-C 见证。

## 真正未覆盖的 constructor

`fixed C -> eta_q/rho_v -> actual final-evaluation D -> (u_v,g) -> localization square + cocycle -> D ∈ permitted output family -> same-M/reference/weights signed readout`.

当前 Lean donor `SourceKummerEvaluationArrows.lean` 只保存 reduced `FPrimeStripEquiv`、unit/Kummer layers、square commutation 和 frozen IPL factorization；源码明确不构造实际 Theorem 3.11 Kummer/evaluation maps、Ind1–Ind3、IPL/SHE/APT conclusion 或 q-to-hull map。`SourceKummerEvaluationSquareExtension.lean` 把 lower strip representative 由已给三条腿强制出来，但不增加 hull/output-family 数据。`C9IUTBridgeOutput.lean` 仍把 `qPilotOutput_mem` 保留为显式 C1 field。

因此本包的实际动作是剪枝，不是再写一份同义证明：关闭重复审查任务，保留上面公式作为 canonical reference，把下一任务限制为寻找这一个 constructor；找不到时报告该具名 source boundary。

## SHEAF 状态

- `statement_compiles`: not applicable（本包为文档去重与公式索引）。
- `proof_body_checked`: not run。
- `kernel_closed`: not run。
- `target_accepted`: false；C1/`FinalEvaluationQMark` 仍 open。
- 本包没有修改 Lean、生产接口、目标定义或数值参数；没有运行 Lean、Project build、comparator 或独立审查。