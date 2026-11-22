# C1 / `FinalEvaluationQMark` 交接总览

日期：2026-10-26。用途：给后续工作提供一个短入口，避免重复最近两天已经完成的 carrier、数值、LANA、A1/A2/A3 和循环论证审查。

**最新复用入口：** [U2K2-SQ3 追踪笔记](C9-U2K2-SQ3-MARKED-TRACE-20261026.md) §6 列出已经尝试并纠正的具体论证，§7 更正映射类型。本轮再次提出“further rigidifications 中必含固定 q”以及泛查闭环，是重复工作，没有新 C1 证明。既有通用运输/cocycle 公式尚未实例化为固定真实 `C` 的 maps；cQ3 对象与实际输出族也不能按定义等同。本文早期“与 A1/A2/A3 独立”只可读作现有证明体不提供该构造，不是完整源理论的逻辑独立性定理。

## 当前判定

1. **A1/A2/A3** 已在接受的 `Theorem311Source.Input` 边界上完成 Lean kernel 闭合；这不是 `OriginalInput -> Input` 的构造。用户已接受该边界，后者不再作为本任务前置。
2. **C1 与 A1/A2/A3 独立。** A1/A2/A3 控制已经存在的输出和体积项，不能产生固定 q 标记进入 final-evaluation 输出族所需的态射。因此不需要先 Lean A1/A2/A3 再做 C1。
3. **paper-level 条件口径：** 若把 Corollary 3.12 的 xi-e/xi-f 当作原文 source assertion，则固定 q 的输出读数投影已经是输入，标量步骤可完成。这个结论不等于独立 Lean 证明。
4. **独立口径的首个缺口：** `XiEToXiFOutputReadoutProjection`，也就是固定 q 的 operation-level 条件如何给出允许的 final-evaluation 输出读数。现有记录没有构造它，故 `FinalEvaluationQMark`/C1 仍 open。

## 最小数学责任

固定完整的 admissible `C`，记实际 final-evaluation 输出族为 `P_C`，归一化读数为 `nu_C`，q 读数为 `Q_C`，hull 上界为 `h_C`。需要证明下列任一项：

```text
exact:  ∃ D ∈ P_C, nu_C(D) = Q_C
signed: ∀ ε > 0, ∃ Dε ∈ P_C, Q_C - ε ≤ nu_C(Dε)
```

同时已有/可复用的是：`∀ D ∈ P_C, nu_C(D) ≤ h_C`。于是 exact 情形直接给出 `Q_C ≤ h_C`；signed 情形若 `Q_C > h_C`，取 `ε=(Q_C-h_C)/2` 即与两侧不等式矛盾。这个标量步骤不需要 A1/A2/A3。

## 已经确认的边界

### 可复用

- 真实 paper IQ/O carrier、`lambda O` hull、加权 `det^M`、原 `O(-)` reference 和 signed degree 的对象层兼容性。
- Remark 3.10.2 的 IPL composite（运输既有 q-pilot 同构类）；有限 `Qp`-代数 hull/Haar transport 及 reference-index 修正。
- Lean 中的 `qPilotPoint = tensorLanding q = tensorUnit` 等 reduction，以及给定 donor/hull 条件时的条件构造。
- `C9C1IdentifiabilityProbe.lean` 的反向检查：membership 本身不推出 `logVol = Q`。

### 不能当成证明

- full-strip/poly-isomorphism、cQ3/cQ4 collection、q-coricity、SHE、抽象 sheaf descent：它们运输或收集已有对象，不自动产生指定 q-to-hull marked arrow。
- “various possibilities for further rigidification”：没有证明固定 q 标记属于受限 final-evaluation family；未标记 transport 也不固定 q-scale。
- reduced C7 的 `tensorUnit ∈ canonicalHull`：这是独立支线，当前没有到 paper-faithful C1 的 verified consumer edge。
- 局部/条件数值（例如 b=3、`B=I`、`rho=1/2`）或旧反证 profile：没有实现同一完整 `C` 的允许输出，因此不能填当前 gap。

## 反循环检查

不要把“membership”“同构类运输”“collection 存在”“读数相等”互相替代。特别是：

```text
q-pilot membership  ≠  q readout equality
full-strip transport ≠  new q-to-hull map
cQ3 collection      ≠  essential-image/final-family membership
xi-f citation       ≠  independent proof of the xi-e -> xi-f projection
```

## 下一步唯一主线

只取一个固定 admissible `C`，沿 Remark 3.10.2 的 `U2 K2` 复合追踪 `eta_q` 到实际 sQ3/further-rigidification 输出，逐项给出：实际像、local structure maps、localization square、overlap cocycle、原 output-family 成员性，以及同一 `M`、`O(-)` reference、weights 和 signed readout。若该 source arrow 不存在于当前源接口，就立即记录边界；随后只尝试同一 `C` 的真实 `S_C ≥ kappa_C` 或 signed-epsilon witness。不要重启 A1/A2/A3、`OriginalInput -> Input`、reduced `tensorUnit` 分支、抽象 sheaf 或数值调参。

## 验收状态

| 项目 | 状态 |
|---|---|
| A1/A2/A3 at accepted Input boundary | `kernel_closed` |
| Paper scalar step assuming xi-e/xi-f | 条件成立 |
| Independent `FinalEvaluationQMark` | `open` |
| C1 target accepted | `false` |
| 本轮 Lean / Project / comparator / independent review | 未运行 |

证据入口：`C9-FINALEVALUATIONQMARK-DEPENDENCY-AUDIT-20261026.md`、`C9-C1-SINGLE-AGENT-NATURAL-PATH-20261026.md`、`C9-C1-MARKED-GATE-RECHECK-20261026.md`、`C9-HULL-CARRIER-SHEAF-DESCENT-20261026.md`。

## 七日资料复核（2026-10-26，复用既有结论）

本节不是新证明，只把 10-24 至 10-26 已有记录的最终结论固定为后续入口：

- `C9-MARKED-IMAGE-DESCENT-20261024.md` 与 `C9-LOCAL-GLOBAL-DESCENT-ATTACK-20261024.md` 已排除“局部相容/collection 存在即可得到全局 q-to-hull 箭头”；给出的算术局部模型只是否定该弱推理，不是完整 IUT 反例。
- `C9-XIF-ATTEMPTS-20261025.md`、`C9-C1-LOCAL/IND/DET/IPL/LOOP/APT-20261025.md` 逐项排除了局部 theta 值等于 hull 读数、IPL 直接保读数、determinant 等式、Ind 闭包、APT fixed-point 等路线。
- `C9-REVIEW-COR312-XIF-20261025.md` 和 `C9-COR312-REVIEW-SUMMARY-20261025.md` 撤回了早期“closed loop 自动给 exact membership”的说法：闭环保留双重 intertwining，但没有给出 q 值落入实际 output readout 的见证或有符号误差。
- `C9-C1-LITERATURE-20261025.md` 记录 LANA 9-1（`eta_q = eta^anab_S`）正是同一兼容性，且报告尚未重建证明；这支持“来源中确实有未展开桥”，不构成反例。
- `C9-HULL-CARRIER-SHEAF-DESCENT-20261026.md`、`C9-C1-MARKED-GATE-RECHECK-20261026.md` 之后只保留条件链：paper IQ/O carrier、hull、det^M、reference 和 readout 可比较；缺的仍是固定 q mark 在受限 final-evaluation family 中的实际 sQ3 attachment，或同一 C 的 signed-epsilon / `S >= kappa` 见证。
- `C9-XIE-SOURCE-CONDITION-AUDIT-20261026.md` 最终分层：xi-e 的 fixed-q 可执行性不是 coverage；xi-e 的 output-link 加 xi-f 的 “constitutes a construction” 才是 `XiEToXiFOutputReadoutProjection(C)` 的 source assertion。

因此后续不得把以下任一项当作该命题的独立证明：A1/A2/A3、full-strip/IPL 同构、cQ3/cQ4 collection、q-coricity、抽象 sheaf descent、局部数值 profile 或 reduced C7 `tensorUnit` membership。

## 目标强度更正：原文的 `R_{≤h}` 不是输出集的定义

复核本地 IUT III 原文 xi-d 后，必须保留一个早期命名差异：xi-d 把 `R_{≤h}` 明确定义为 `{λ ∈ ℝ | λ ≤ h}`，即实数半直线；它不是“实际输出读数集合” `R_possible := {ν(D) | D 是允许输出}`。所以论文末尾的 `Q ∈ R_{≤h}` 是标量不等式 `Q ≤ h`，并不单凭集合记号给出 `∃D, ν(D)=Q`。xi-e/xi-f 对“输出可能性构成 q-pilot 读数之构造”的叙述仍是待解释的来源桥，但 exact attainment 与 signed-epsilon output family 是可用的充分证书，不可未经证明就当作原文唯一/必要目标。阶段 2 冻结 Lean 类型前，应明确 `XiEToXiFOutputReadoutProjection(C)` 是直接的 paper scalar projection，还是更强的 actual-output witness theorem；不能把 `R_possible` 偷换成原文的 `R_{≤h}`。这项语义更正不关闭该 source bridge，也不改变 open 状态。
