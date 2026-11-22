# C9 hull/carrier gate：自然语言收口与最小 source 命题

日期：2026-10-26；owner：root 单 agent；状态：paper-level carrier route closed,
fixed-q source landing open。本文只记录本轮自然语言推导，不新增 Lean 定义，不把
`xi-f` 结论改名为独立证明。

## 1. 先分清三个同名问题

仓库中至少有三个容易被叫作 C1 的东西：

1. 旧 N8 `SourceInputBinding`：地方、选定 realization 和 prime-strip fiber 的接线；
2. 当前 value-monoid `sourceHolomorphicHull` 的有限性诊断；
3. Corollary 3.12 所需的 fixed-q membership：固定 q-pilot 的 signed readout 是否
   落在实际 final-evaluation output readout family，或至少有源允许的有符号逼近。

本记录讨论第 2、3 项。第 2 项的 Lean 结论
`degreeFaithful -> sourceHullVolume = top` 是当前 value carrier 的形式化障碍，
不是论文 IQ/O carrier 的反例。第 3 项才是标量比较 `Q <= h` 的 source gate。

## 2. 论文载体层的自然语言证明

固定一份合格的完整初始数据 `C`，固定 q-pilot、Theta-gluing、procession 权重、
共同 tensor power `M`、`O(-)` reference 和原文 normalization。记：

* `E`：Theorem 3.11(i)(a) 的实际 IQ/log-shell tensor carrier；
* `O_E`：其 mono-analytic integral structure；
* `P_C`：实际 final-evaluation 允许的 output regions；
* `H_C = hull(P_C)`：Remark 3.9.5(i) 的最小 `lambda O_E` holomorphic hull；
* `nu_C`：先取 `det^M`、再按 Ob3/reference 和 procession 权重归一化的 signed
  log-volume；
* `Q_C`：q-pilot 在同一 reference/normalization 下的 signed readout。

第一步，`O_E` 对乘法稳定，所以每个 output hull 的 `det^M` 是 q-codomain
local/global Frobenioid 的合法对象。cQ3 的 local-global collection 记录局部
structure-poly-morphism、global object 和 localization isomorphisms；cQ4 的
log-Kummer adjustment 只改变允许的 vertical shift。它们保证输出对象和 q 对象
在同一个可比较的 determinant/reference 框架中。有限 etale `Qp`-代数同构保持
integral closure、fractional-ideal hull；Haar 缩放在单位相对 signed log-volume
中抵消。若 reference lattice 不是 `O_E`，唯一修正是实际指数

```text
delta = (log [f(R):L] - log [R':L]) / dim_Qp(E),  L = f(R) ∩ R'.
```

这个 `delta` 由真实参考格决定，不能按 gap 选择。

第二步，hull 的最小性和 Haar 单调性给出

```text
forall D in P_C,  nu_C(D) <= nu_C(H_C) =: h_C.
```

到这里，carrier、hull、determinant、reference 和 readout 的类型已经相容；并不
需要、也不能要求把整个 degree-faithful value monoid hull 等价到有限 IQ hull。

## 3. q-mark 的 sheaf/stack 接合责任

Remark 3.10.2 的交换方形把 IPL 复合约化为同一个 `U2 K2`。完整
`F^turnstile-times-mu` prime-strip 同构会运输由 splitting generator 与 `rho_v`
决定的 q-pilot 同构类。这个运输本身是有效的，但它只说“已给对象的同构类可以
运输”。

真正需要的 source 命题是下面的 `FinalEvaluationQMark`：

```text
对于每个合格 C 和每个 eps > 0，存在 source-allowed D_eps，使得
  D_eps ∈ P_C,
  Q_C - eps <= nu_C(D_eps),
  nu_C(D_eps) <= h_C。
```

若 source 能给零误差，则可加强为 `exists D in P_C, nu_C(D) = Q_C`；这不是必须
的强目标，因为原文 xi-f 明确留下了“perhaps only up to some sort of approximation”。

在 sheaf 语言中，`FinalEvaluationQMark` 要求：

1. 每个 place 的 transported q-mark 有一个到 output hull determinant 的真实局部
   structure map；
2. 这些 maps 与 q/Theta localization squares 相容；
3. overlaps 上满足 cocycle；
4. 局部 collection 在原 output family 中有效下降，而不是只在 sheafification
   中产生一个新对象；
5. 下降后的对象读数使用原 `M`、reference 和 procession normalization。

`cQ3` 规定了 collection 和 compatible morphism 的范畴，但不从 collection 对象
自动产生第 1 步的 global map。若写局部乘子 `u_v`、全局分量 `g`，最小方形是

```text
loc_v(g) ∘ lambda_q,v = lambda_H,v ∘ u_v.
```

没有这个由 source construction 提供的方形，局部 maps 仍可能有
`h - Q = S - kappa`，其中 `S >= 0` 而 `kappa` 未受控制；此前
`C9-LOCAL-GLOBAL-DESCENT-ATTACK` 的 `Q/3` 例子正是排除“局部 collection
存在即可全局化”的弱推理。`kappa = 0` 不是必要条件；真实 source 只需证明
`S >= kappa` 或给出真正的 escape/epsilon witness。

## 4. 标量结论的严格自然语言证明

一旦 `FinalEvaluationQMark` 由 source construction 提供，结论只有两行：若
`Q_C > h_C`，取 `eps = (Q_C-h_C)/2`。则

```text
Q_C - eps > h_C >= nu_C(D_eps),
```

与 `Q_C - eps <= nu_C(D_eps)` 矛盾。因此 `Q_C <= h_C`。零误差成员关系是这个
论证的特例。

注意这不是把 `Q_C` 反向定义成某个 output 的读数；`D_eps` 必须来自实际
final-evaluation family，`nu_C` 必须已经固定 reference、weights 和 `M`。

## 5. 原文 xi-e/xi-f 在逻辑上的准确位置

IUT III xi-e 说 output readout family 通过 IPL 与 input prime-strip 的 pilot
readout 相联系；xi-f 随后直接断言该构造构成 input pilot log-volume 的构造（允许
未量化的 approximation），并形式上得到 `Q_C in R_{<=h_C}`。因此：

* **接受 xi-e/xi-f 作为原文 source assertion 时**，上面的 `FinalEvaluationQMark`
  已由原文承担，`Q_C <= h_C` 的自然语言证明闭合；
* **要求独立于 xi-f 的推导时**，xi-e/xi-f 本身就是需要证明的 source gate，不能
  再从 A1/A2/A3、APT、SHE、IPL、cQ3 或 full-strip equivalence 单独推出。

这两个判断不矛盾：C1 不是 A1/A2/A3 的逻辑后果，但在论文叙述中它也不是另加的
假设，而是 xi-e/xi-f 所承担的最后 source 断言。

## 6. 对 Lean 路线的决定

`C9A1A2A3Source.lean` 已在用户接受的 `Theorem311Source.Input` 边界闭合；它
不是 C1 的 proof dependency，也无需先重做。Lean 的最小真实目标应是一个
`FinalEvaluationQMark` 语句，使用实际 output family、IQ/O carrier、determinant、
reference 和 signed readout，并把 approximation 量化。不能用 `Nonempty`、singleton
possible-output、自由 `qPilotAsOutput` 字段或当前 value-monoid hull 填充。

当前 reduced files 的精确边界是：`SourceKummerEvaluationArrows` 有 Kummer/evaluation
方形和 IPL factorization 的条件接口；`SourceArithmeticHolomorphicLanding` 的
`SourceLocalizationExpressible` 以 zero bundle 可满足，只表达 reduced landing，
没有 rank/module/determinant/source q-map。因此它们还不能 inhabit
`FinalEvaluationQMark`。

最终方向：先完成这个 source landing/marked descent；之后才能把 C1 报成
`kernel_closed`。在此之前，正确报告是“paper carrier object compatibility 已经
自然语言闭合，fixed-q source membership 仍 open”，而不是再扩展 A1/A2/A3。

## 7. 原文层面可以怎样把这一步说成一条不循环的证明

继续读 III Remark 3.12.2(fitw) 后，原文自己的逻辑桥可以精确写成：

```text
q-intertwining
  => q-intertwining ∧ Theta-intertwining/indeterminacies
  => Theta-intertwining/indeterminacies,
```

其中第一个箭头是 Theorem 3.11 的 multiradial representation 经过 sQ1--sQ4
subquotient 操作的内容，第二个箭头只是合取消去 q 分量。这里保持不变的是同一
个抽象 `F^turnstile-times-mu` prime-strip；改变的是它在两种 arithmetic
holomorphic structure 下的 intertwining。于是 q-intertwining 不是从 output
数值反推出来的，而是算法在构造 Theta-intertwining 时保留的输入约束。

在这个原文语义下，`xi-d` 的 `R_{<= -|log(Theta)|}` 是所有经 hull、determinant、
log-volume 投影得到的 Theta-side readout；`xi-e` 说这些操作是在 q-intertwining
固定为 `-|log(q)|` 的条件下可执行；`xi-f` 只是把 fitw 的 q 分量投影成数值，允许
Ind1--Ind3 的近似。因此 paper-level 的 C1 不是另一个独立假设：它是
“固定 q-intertwining 的 output projection”这一 source theorem 的数值投影。

这条说法仍不能把 Lean 当前的 reduced records 当成证明，因为要把 fitw 的逻辑
箭头展开，必须给出实际 q-mark 的 localizations、sQ3 structure maps、cocycle 和
共同 reference。换句话说，原文层面的自然语言证明现在可以闭合；Lean 层面的
`FinalEvaluationQMark` 仍是对这条 source theorem 的忠实形式化责任，而不是新的
数学前提，也不是 A1/A2/A3 的前置。

## 8. 单 agent 复核：sheaf 证明链的实际闭合点

为避免把“载体可比”再次误写成“q 已落入输出”，把 sheaf 路线写成一个可逐项验收
的命题。固定完整合格数据 `C`，在 places/labels 的覆盖上定义 `H_C(U)`：对象是
实际 evaluation 输出在 `U` 上的 `det^M` hull、原 `O(-)` reference，以及一个
从 q-pilot line 的限制到该 hull determinant 的 structure-poly-morphism；限制映射
是原 localization。若 source 真正给出

1. 每个局部 `lambda_q,v : L_q,v -> D_H,v`；
2. `loc_v(g) ∘ lambda_q,v = lambda_H,v ∘ u_v` 的 localization 方形；
3. 重叠处的 equality/cocycle；
4. 下降对象仍属于原 final-evaluation family；
5. `M`、reference、weights 和 signed readout 沿下降保持不变，

则有效下降定理给出一个 global `lambda_q : L_q -> D_H` 及一个实际输出
`D_eps`（零误差时就是 `D`）。hull 最小性给出 `nu(D_eps) <= h_C`；同一
determinant/reference 方形给出 `Q_C-eps <= nu(D_eps)`。若假设 `Q_C > h_C`，
取 `eps=(Q_C-h_C)/2`，便有

```text
Q_C-eps > h_C >= nu(D_eps) >= Q_C-eps,
```

矛盾。这是一个真正的 sheaf/stack 证明，而不是把 q 的数值反向定义为某个输出。
exact membership 只是 `eps=0` 的特例。

逐项核对原文后，`cQ3` 给出的是 `H_C` 的 local/global collection 范畴，
`cQ4` 给出 vertical log-Kummer compatibility，Remark 3.10.2 与 IPL 给出
full-strip 上的 pilot 同构类运输；它们没有在现有文本/Lean 接口中给出上述第 1
步的指定 q-to-hull map，也没有自动把 collection 对象变成第 4 步的原输出成员。
因此这条 sheaf 证明在数学上已把责任压缩到一个最小 source 命题
`FinalEvaluationQMark`，但在独立于 xi-f 的口径下仍未闭合。

验收口径必须分开：若把 xi-e/xi-f 作为原文 source assertion 接受，它正是
`FinalEvaluationQMark`（允许 approximation）的来源，上面的标量反证立即闭合；
若要求从 A1/A2/A3、APT、SHE、IPL、cQ3、cQ4 独立推出，则当前资料不足，C1
仍是 fixed-q essential-image/source-landing 缺口。两种口径不矛盾，也不改变
A1/A2/A3 已在接受的 `Input` 边界闭合且无需先行证明的结论。

## 9. 本轮直接重跑的自然语言证明：闭环与载体态射分开

本轮只追原文最可能承载证明的箭头，没有重做数值、A1/A2/A3 或局部—全局反例。
核对的是 IUT III Remark 3.9.5(vii)-(ix)、Remark 3.10.2、Theorem 3.11(i)-(iii)、
Remark 3.11.1(iii)-(v)、Corollary 3.12(xi-c)-(xi-f)，并沿用 10-24 的
`LOCAL-GLOBAL-DESCENT` -> `MARKED-IMAGE-DESCENT` 纠偏。

固定一份原文允许的完整数据 `C`。令 `P_C` 为实际 multiradial/final-evaluation+产生的可能区域族，`H_C=phi(P_C)` 为原文在 IQ/O carrier 上的最小 hull。自然语言证明+中已经可以无缺口推出：

1. 每个 `P in P_C` 都包含于 `H_C`；`O`-稳定化、加权 `det^M` 和原 `O(-)`
   reference 把 hull 读数变成可与 q-pilot 比较的同一 Frobenioid 线对象。
2. 用同一权重、`M`、reference 及 signed normalization，单调性给出每个实际输出+   `nu_C(P) <= h_C`。有限 Qp 代数同构下整数闭包、hull 和单位相对 Haar 读数的运输，
   复用已经证明的算术 lemma；其他参考格保留精确指数修正 `delta`。
3. Remark 3.10.2 的六段 diagram composite，由下方前两箭头的逆、第一条 Kummer+   竖箭头和上方三条 evaluation 箭头组成。它给出实际的 full prime-strip poly-isomorphism；
   Remark 3.11.1(iii) 的 IPL 把输出 strip 连到固定 q 输入 strip，II.4.9(viii) 的 pilot+   定义使 splitting generators 与 `rho_v` 的同构类随之运输。
4. 到 sQ3 时，cQ3 要求 hull determinant 的对象带 `structure poly-morphism`；sQ4 的
   cQ4 保留 log-Kummer 相容性。先经过 sQ3/sQ4 再到 sQ5，正是 Remark 3.9.5(ix)
   所说 closed loop 的顺序。若该结构态射确实把固定 q-pilot 接到 `H_C`，就可在同一
   signed degree 中比较；全局有效线对象态射给 `Q_C <= h_C`。较弱的真实近似族
   `Q_C-eps <= nu_C(D_eps) <= h_C` 也足够，取 `eps=(Q_C-h_C)/2` 即矛盾。+
这是一条完整的**条件证明**，但第 4 步的 antecedent 不能由前 3 步的类型/同构信息+自动删掉。Remark 3.11.1(iii) 明说 IPL 是 strip 的 full poly-isomorphisms；Remark+3.11.1(iv) 同时提醒 APT 的可能区域通常还需 Remark 3.9.5(vii) 才能与 codomain+对象比较。cQ3 定义的是带到 hull 的态射的类别和 local-global collections；集合中有+对象，不等于固定 q-pilot 已带着该指定态射属于它。cQ4 可运输已有箭头，不能造出+尚未给出的箭头。该类型差异也正是 10-24 `MARKED-IMAGE-DESCENT` 中+`h-Q=S-kappa` 账目的来源。+
所以本轮**没有得到独立于 xi-e/xi-f 的 C1 证明**。更精确地说：若把 Remark+3.9.5(ix) 的 closed-loop 断言解释为已经包含这个 q-to-hull structure map，或者直接接受+Corollary 3.12(xi-e)/(xi-f) 的输出投影，paper-level 的标量推导就闭合；但这时被接受的+source assertion 已经承担了争议中的相容性责任，不能再说是从 cQ3/cQ4/IPL/SHE+独立导出。若不接受该断言，现有可见定义中没有构造 `lambda_q,v`、定位交换方形、
cocycle、原输出族成员性和原 reference 下的读数。因此 §7 中“原文层面的自然语言证明现在可以闭合”应限缩为“接受 xi-e/xi-f 时条件闭合”；不能作为独立证明结论。+
下一项只做一个源构造：在同一固定 `C` 上，把 transported `eta_q` 的实际像写到+sQ3 的 `Aut(det^M(H_C))`-orbit structure morphism 中，逐处给 `lambda_q,v` 和+localization square；证明这些态射满足重叠 cocycle，下降后仍是原 final-evaluation 允许对象，并逐项保留 `M`、`O(-)` reference、权重和 signed degree。若原文算法只给 collection 而不给这条箭头，则改走同一 `C` 的实际 `S_C>=kappa_C` 或 signed-epsilon output 证书；不再把 strip 等价当作线态射，也不把 xi-f 当证明。+
本轮为单 agent 原文/仓库记录核对；未运行 Lean、Project build、comparator 或独立审查。`n8-c9-final-evaluation-capsule` 仍 stage1 open，`target_accepted=false`。A1/A2/A3 的 Input-boundary 结果和 `OriginalInput -> Input` waiver 均未改动。

