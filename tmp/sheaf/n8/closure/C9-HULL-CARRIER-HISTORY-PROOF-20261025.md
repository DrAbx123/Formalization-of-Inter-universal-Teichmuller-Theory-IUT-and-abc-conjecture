# C1 hull/carrier：跨日期复用与自然语言证明核查

任务：n8-c9-hull-carrier-compatibility；owner：本 chat root；日期：2026-10-25。
阶段：SHEAF stage 1（进行中）。消费者：论文 Cor. 3.12 的有限有符号 hull log-volume，以及 C9 的 q ≤ h 比较。

## 冻结范围

本包沿 10 月 16–25 日已有记录追踪 actual final-evaluation region → actual tensor carrier → paper λO-hull → 同一归一化 log-volume。不重启 A1/A2/A3 或已豁免的 OriginalInput → Input；不以 arbitrary data、ray packet 或另一个 carrier 偷换源对象。

主读文件：SourceK1K2ActualTuplePacket、SourceK1K2HullPresentationFamilyCutActual、SourceProcessionFromContract、SourceLogShellActualTensorSpan、FinitePlaceStepVAssembly、SourceTheorem311ReferenceContract、SourceInternalWiring、SourceValueHullRealizationBridge，以及对应早期协调笔记与 AUDIT_LEDGER。

写入范围：本记录、配套 evidence JSON、AUDIT_LEDGER 追加、本节点 JSON 的研究补充、STATE/queue 追加。不改生产 Lean 定义；不声称旧 value hull 与有限 paper hull 等价。

数学量词：固定论文允许的完整输入、place、label、output capsule、原权重与归一化；核查所有允许 choice 的区域和共同 ambient carrier，不能仅造一个方便的样例。

statement dependencies：实际区域与 tensor block 的定义；paper λO-hull 的含义；参考测度、determinant 和原 normalization。
proof dependencies：历史的实际有限地方 tensor/Haar/finite-index 定理；任何尚无 source constructor 的箭头保留为 gap。

验收：给出可逐步检查的自然语言证明或首个缺失构造；逐项标注历史已证明、当前复核、条件和开放。此次不预告 Lean 编译/比较器成功。

一个只读复用 agent 核查 10 月 16–18 日 source 接入；root 核查后续 Lean 类型、论文定义和可证明的 carrier/hull 运输。

## 证据核查结果

### 1. 已有的真实算术载体结果

下列结果是实际有限地方对象上的结果，不能再归类为 toy carrier：

* `FinitePlaceArithmeticIQTensor.lean` 定义实际有限完备化 packet 的
  `ArithmeticPacketTensor`、实际 integral log-shell region，以及其 `ℚ`-span
  `arithmeticIQCarrier`；非空有限族时证明该 span 是整个 packet tensor。
* `FinitePlaceArithmeticTensorBlocks.lean` 将 packet tensor 实际分解为按 place
  tuple 的 `ArithmeticTensorTupleBlock`，并证明纯 tensor log-region 的投影像等式。
* `FinitePlaceArithmeticIQHull.lean` 对实际 integral log-region 构造 field-product
  分解下的 `hull`，证明 compact、正且有限的 Haar measure，以及 `λ·O` 形式。
* `FinitePlaceArithmeticTupleCanonicalHull.lean` 用分解无关性构造 canonical hull 与
  unit reference，并证明相对 Haar/log-volume 不依赖 field-product 分解。
* `FinitePlaceArithmeticTupleHullTransport.lean` / `...IQHullTransport.lean`
  证明连续 ring equivalence 运输 hull，并保持 unit-relative normalized log-volume。
* `FinitePlaceIntegerTensorComparison.lean` 和
  `SourceK1K2ActualTuplePacket.lean` 进一步给出实际整数 lattice、finite-index
  分解和 `p^n` scaling 的精确 log-volume 变化。

这些定理完成了下面这条**算术侧**链：

```text
actual finite completion packet
  -> actual integral log-shell tensor region
  -> canonical λ·O hull in a finite product of local fields
  -> positive finite Haar measure
  -> decomposition-independent normalized log-volume.
```

它们没有构造 Theorem 3.11 的 final-evaluation output region，也没有把 source
theta-pilot point 放进这个 tensor block。

### 2. 旧 value-monoid hull 的确定性诊断

`SourceImageHull.lean` 把 `ThetaPilotPoint` 定义成 value monoid 的函数，并把 hull
定义成对所有非单位 componentwise scaling 闭合的最小 submonoid；
`SourceImageHullVolume.lean` 定义其 log-volume 为 hull 中 point log-degree 的
上确界。`C1FiniteHullObstruction.lean` 的无 `sorry` 定理给出：若 pointwise
degree-faithfulness 成立，则该 hull 的 log-degree 无界，故 `sourceHullVolume = ⊤`。

自然语言证明：令 `N = card(SourceVolumeIndex l)>0`。任取 `a>0`，令 `s_a` 的每个
component 为 `posRealAction(ofAdd a)`。faithfulness 使每个 component 非单位，故
`s_a` 是合法 scaling。零标签 theta point 在 hull 中，hull 的 scaling closure
使 `s_a*x₀` 在 hull 中；加法性给出

```text
logDegree(s_a*x₀) = N*a + logDegree(x₀).
```

令 `a` 趋于无穷，hull 中的 log-degree 无界，而 `sourceHullVolume` 正是这些
`ENNReal.ofReal` 的上确界，所以等于 `⊤`。这不是论文的反例，而是证明当前
value-carrier 不能同时代表“所有非单位 scaling”与论文需要的有限 `λ·O` hull。

同一矛盾已在 `SourceArithmeticThetaPilotBridge.lean` 中以更强的 bridge 形式
封装：若 arithmetic canonical hull 的 bounded degree units 覆盖整个 source
hull，并且 degree readout 相容，则可推出 source hull finite；在 faithfulness 下
该 cover 与 `unit_bound` 互相矛盾。因此继续寻找一个把**整个** value hull 映到有限
arithmetic hull 的 map 是错误目标。

### 3. 论文原文的正确兼容性命题

IUT III 原文（`IUT-III.txt`，xi-c/xi-d，当前冻结版本）给出的对象关系是：

1. Theorem 3.11 的 algorithm 产生 output possibilities in `1,∘U`；SHE 说这些
   output 以 `1,∘` arithmetic holomorphic structure 的 localizations 表达。
2. 形成 holomorphic hull 后，output 不再被要求直接作为各种 local-field tensor
   regions 比较，而是表达为 arithmetic vector bundles 的 localizations over
   `O_{K_v}`。
3. q-pilot 的 representation 与 output hull 在共同的 `1,∘U_Q` 中比较；output
   侧是 rank `>1` bundle，q 侧是 arithmetic line bundle。
4. 对 output 侧取合格的正 tensor power，再取 determinant；随后对 output region 与
   q-pilot region 使用**同一个 procession-normalized log-volume**。
5. 这一步只产生实数 readout：possible output readouts 组成
   `R_{≤ -|log Θ|}`，而 q-pilot readout 是 `-|log q|`。xi-f 的结论是后者属于
   前者，因而 `-|log q| ≤ -|log Θ|`。
6. Remark 3.11.1(iv) 明确 APT 不是把一个 set-theoretic region 用函数直接运输
   到另一个 carrier；它是同时相对于两边 arithmetic structures 可执行的构造算法。

所以本 gate 的原文忠实陈述应是：

```text
output hull --(determinant + positive tensor power + normalized readout)--> ℝ
q-pilot region --(same determinant/readout)-------------------------------> ℝ
```

并证明两者使用同一个 `1,∘U_Q` normalization。它不是
`sourceHolomorphicHull ≃ arithmeticTupleCanonicalHull`，也不是
`sourceHolomorphicHull` 的点集包含在 `arithmeticTupleCanonicalHull` 中。

### 4. 非循环的自然语言证明（正确 gate）

固定一个允许的 source input、一个 `v_Q`、一个 label `j`，并固定原文的
procession weights 与 determinant normalization。令：

* `E` 是 actual IQ/log-shell tensor carrier；
* `H_E` 是由 actual integral log-shell region 取出的 canonical `λ·O` hull；
* `U_out` 是 final evaluation 给出的某个 output possibility 在 `1,∘U` 中的
  arithmetic localization；
* `U_q` 是 q-pilot 在同一 `1,∘U_Q` 中的 representation；
* `ν` 是同一 normalized determinant/log-volume readout。

证明分五步：

**(i) Arithmetic hull bound.** `U_out` 被 `H_E` 包含，或更精确地，其 determinant
positive tensor power 被 `det(H_E)` 包含。因为 `H_E` 是 candidate `λ·O` hull，
holomorphic hull 的最小性给出 `Hull_E(U_out) ⊆ H_E`。Haar 单调性和 determinant
normalization 给出 `ν(U_out) ≤ ν(H_E)=h`。这一步完全使用已有 actual IQ hull、
measure、transport 定理；不涉及 value-monoid hull。

**(ii) q-pilot landing.** q-pilot representation `U_q` 位于同一个 `E`/`1,∘U_Q`
normalization 中，而不是被强行放进小 log-shell carrier。其 determinant/readout
由 q-pilot line bundle 的 arithmetic degree 定义。

**(iii) q readout.** Proposition 3.9 的 global-degree/log-volume dictionary，
连同 q-pilot 的 fixed input prime-strip normalization，给出 `ν(U_q) = Q`，其中
`Q=-|log q|`。这不是“存在某个输出 log-volume 等于 Q”的假设，而是对已经确定的
q-pilot representation 的 readout 计算。

**(iv) final evaluation compatibility.** Theorem 3.11 final evaluation/Remark
3.11.1(iii) 给出 output possibilities 与 q-pilot prime-strip 的 IPL/SHE linkage，
并允许以 pilot object 的 rigidification 作为一种 possibility。于是 `U_q` 对应的
readout 属于同一 output-readout family `R`。这一步不是 A1/A2/A3 的抽象后果，必须
由实际 final-evaluation construction 提供。

**(v) scalar conclusion.** 由 (i) 对 family 中每个 readout 有 `r≤h`，由 (iii)-(iv)
有 `Q=ν(U_q)∈R`，故 `Q≤h`。这正是 xi-f/Cor.3.12 所需结论；无需先构造一个
`D∈O` 满足 `logVol(D)=Q` 的 exact representative。

该证明没有把结论放进结构字段：`U_out`、`U_q`、determinant map、readout equality
和 family membership 都是五步中必须独立构造的对象/命题。

### 5. 每一步在当前仓库的精确状态

| 自然语言步骤 | 当前证据 | 状态 |
|---|---|---|
| actual `E`、integral region、canonical `H_E`、finite Haar/readout transport | `FinitePlaceArithmeticIQTensor`, `...IQHull`, `...TupleCanonicalHull`, `...HullTransport` | 已证（算术侧） |
| `U_out` 从 final evaluation 落到 `E`/`1,∘U` | `SourceArithmeticHolomorphicLanding` 只有 reduced localization record；没有 rank/module/determinant landing | 缺 source constructor |
| `U_q` 在同一 `E` 的实际 representation | `SourceKummerEvaluationArrows`/`SourceLogShellActualTensorSpan` 有局部 shell/K1-K2 和 tensor span；没有 q-pilot-to-IQ map | 缺 source constructor |
| determinant + positive tensor power + normalized readout | 论文有定义；仓库有局部 Haar/determinant 供体，但没有把 final output bundle 接上 | 缺组合定理 |
| `ν(U_q)=Q` | q-side scalar / local normalization 有局部结果；global procession-normalized readout 未接到 actual `U_q` | 缺 global readout bridge |
| q rigidification belongs to final-evaluation family | `C9-C1-FULL-TH310-BASIS-20261025.md` 已定位原文依据；Lean 无 family/rigidification object | 缺 source constructor |
| `ν(U_out)≤h` for all possibilities | actual IQ hull monotonicity可用；需要 output landing 与共同 normalization | 条件可证，source landing 缺 |

### 6. Gate verdict and next executable action

语义上，兼容性 gate 已经被确定为“determinant/readout compatibility”，而不是
value-hull 到 IQ-hull 的点态等价；这一步由原文 xi-d、Remark 3.11.1(iv) 和
当前 value-hull no-go 共同确定。算术侧 carrier/hull/measure 也已有真实闭合结果。

**仍未完成的不是 A1/A2/A3，而是一个单一 source-level landing 包：**

```text
FinalEvaluationCapsule
  -> arithmetic localization U_out / q-pilot region U_q in the same E
  -> determinant + positive tensor power
  -> procession-normalized readout ν
```

该包必须至少携带：

1. actual output/rigidification family 与 q-pilot possibility 的成员证明；
2. output 与 q region 到共同 `E` 的实际 source map（允许是 bundle localization，
   不能只是 `Function` 字段无语义）；
3. determinant/power 的 compatibility；
4. `ν(U_q)=Q` 与 `ν(U_out)≤h` 的独立证明。

在这四项存在前，继续补 A1/A2/A3、继续计算局部数值 gap、或把
`sourceHolomorphicHull` 强行接到 canonical IQ hull，都不能推进 C1。此结论不是
停止研究，而是把下一包从“构造一个不存在的全 hull map”收敛到
`FinalEvaluationCapsule → common E → determinant/readout`。
