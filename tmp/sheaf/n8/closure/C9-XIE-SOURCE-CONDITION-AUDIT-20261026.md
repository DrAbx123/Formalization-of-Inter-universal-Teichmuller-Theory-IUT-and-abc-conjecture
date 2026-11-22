# xi-e 是前提、定义，还是来源结论？

日期：2026-10-26。范围：只核对 IUT III Corollary 3.12 的 xi-a--xi-f、Theorem 3.11、Remark 3.11.1 和 Remark 3.9.5；不重做 A1/A2/A3、数值分支或整个 IUT 构造。

## 直接结论

**xi-e 不是 Corollary 3.12 另加的外部假设。** Corollary 3.12 的明确入口是“处于 Theorem 3.11 的情形”（`IUT-III.txt` 约 10152--10180）。xi-e 出现在该推论的证明内部，并以 “let us recall” 的方式把 SHE 和固定 q-pilot 读数的关系写出来。

但“xi-e 不是外部假设”不等于“xi-e 已被前文展开证明”。它有三层内容，必须分开：

1. **输入定义层（可直接复用）：** q-pilot 的读数被定义为 `-|log(q)|`，并由 1-column arithmetic holomorphic structure 与输入 `F^...-prime-strip` 联系起来（xi-e，约 10682--10687）。
2. **SHE 条件层（来源性质/重述）：** “relative expressibility” 被解释为即使在 pilot log-volume 等于固定 `-|log(q)|` 的条件下，相关操作仍有效、可执行、良定义（约 10688--10695）。这说明算法可以在该 q 条件下运行；它不是“输出读数等于 q”的结论。
3. **覆盖/读出层（真正的桥）：** xi-e 随后声称算法、hull、log-volume 产生的输出读数集合与 q 读数通过 prime-strip 同构相联系（约 10696--10704），xi-f 又声称这些输出可能性构成 q 读数的构造，允许各种 indeterminacies 下的 approximation（约 10705--10715）。这才是 `FinalEvaluationQMark` 所需的内容。

因此，若把整段 xi-e/xi-f 当作输入，后面的标量不等式当然无需再争；但那等于把争议中的 q-output projection 当作 source theorem 输入。若只把 xi-e 的“固定 q 条件下操作有效”当作输入，不能推出 q 读数属于输出集合。

## 一个最小逻辑检验

令 `P_C` 是固定 `C` 的实际输出读数集合，`Q_C` 是 q 读数，`h_C` 是 hull 上界。SHE 条件只表示算法在参数 `Q_C` 下有定义；它没有逻辑形式

```text
Q_C ∈ P_C                 (exact)
或
Q_C ∈ closure(P_C)        (approximate).
```

例如完全可以有“算法在 `Q_C=1` 条件下有效”而 `P_C={0}`；这不违反 SHE 的字面条件，却不能推出 `Q_C≤h_C`。所以不能把 E2（SHE fixed-q condition）改名为 `FinalEvaluationQMark`。

## 原文来源的最小依赖链

如果按作者的 paper-level 语义接受 xi-e/xi-f，则最短链是：

```text
Theorem 3.11 hypotheses
  -> Theorem 3.11 output algorithm + IPL/SHE/APT
  -> sQ1--sQ4 and cQ3/cQ4 preserve the q-intertwining
     (up to Ind1/Ind2/Ind3)
  -> xi-e: the fixed-q arithmetic-holomorphic interpretation
  -> xi-f: output readout construction covers Q_C
  -> hull upper bound for every output
  -> Q_C <= h_C.
```

原文还在 Remark 3.12.2(fitw) 将其概括为

```text
q-itw -> (q-itw ∧ Theta-itw/indets) -> Theta-itw/indets,
```

并说第二个蕴含形式上成立、Corollary 3.12 基本形式地跟随。这个表述是来源解释，不是当前 Lean 已检查的 local/global descent 构造。

独立形式化时，真正需要补的最小命题不是“再造整个 IUT”，而是对每个合格固定 `C` 给出：

```text
XiEToXiFOutputReadoutProjection(C):
  Q_C ∈ { nu_C(D) | D ∈ P_C }
  或
  ∀ ε > 0, ∃ Dε ∈ P_C, Q_C - ε ≤ nu_C(Dε).
```

再加已经可复用的

```text
∀ D ∈ P_C, nu_C(D) ≤ h_C,
```

即可用 exact 读数或 midpoint contradiction 完成 `Q_C ≤ h_C`。

这项最小命题可以由一条充分的 source 路线证明：固定 q 标记经过实际 `U2 K2`/IPL 复合进入 sQ3 的 hull-determinant 对象，保留 localization square、overlap cocycle、原 output-family 成员性和同一 `M`/`O(-)`/weights/readout。它也可以由同一 `C` 的 signed-epsilon 输出或 `S_C ≥ kappa_C` 账本替代。它不是 A1/A2/A3 的后置条件。

## “能不能造 C”的范围澄清

- 若 `C` 指 Theorem 3.11 的完整 admissible source datum，xi-e/xi-f **不构造 C**；Corollary 3.12 从“处于 Theorem 3.11 情形”开始，`C` 必须先给出。
- 若 `C` 指我们当前的 C1 compatibility certificate，那么 xi-f 的 source-level 内容实际上就是这个 certificate 的核心；把它作为输入会让 C1 立即成立，但不能再称为从前文独立推出。

## 当前分类

| 项目 | 分类 |
|---|---|
| Corollary 3.12 入口 | Theorem 3.11 hypotheses |
| q 读数与输入 prime-strip 的定义联系 | source definition / source input |
| SHE 在固定 q 条件下有效 | Theorem 3.11/Remark 3.11.1 的 source property |
| 输出读数覆盖 q 读数 | xi-e/xi-f source assertion；独立展开仍 open |
| `Q_C <= h_C` 的实数步骤 | 在覆盖命题和 hull 上界之后形式闭合 |
| 当前 Lean 的 `FinalEvaluationQMark` | 未构造；`target_accepted=false` |

结论：作者没有在 Corollary 3.12 的假设栏里偷偷新增一个名为 xi-e 的假设；作者把它当作 Theorem 3.11 及其 SHE/IPL/cQ3/cQ4 机制的证明性结论来使用。但对我们要做的独立 Lean 证明，必须把“fixed-q operation validity”和“q-readout output coverage”分成两个具名定理，不能把前者直接当成后者。

验证：本记录只核对原文和既有审计，未运行 Lean、Project build、comparator 或独立审查。

附：`C9XiESourceConditionLogic.lean` 已针对上述纯逻辑边界编译通过（exit 0）。它只证明 exact/signed coverage 加上界足以推出不等式，并给出 fixed-q executability 不推出 coverage 的集合论反例；不包含 IUT 对象或 source axiom。
