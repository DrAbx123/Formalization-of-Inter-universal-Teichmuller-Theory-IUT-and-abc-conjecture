# C9-C1 决策综合：先检查载体，再决定 q-pilot 兼容

日期：2026-10-25。本文只综合仓库中已经完成的调查和闭合定理，不重新启动
`C9-C1-NEW-TOOLS`、LANA eta、局部下降、Tannakian、数值反证等已排除路线。
状态仍为 `target_accepted=false`。

## 一、仓库中实际存在的四个“C1”相关目标

必须把以下目标分开，否则会把独立的缺口误接成一条前置链。

1. **旧 N8-C1：`SourceInputBinding`**。它绑定地方、选定 realization 和
   fiber 比较，是构造当前 q/hull bridge 数据的接线之一；
   `C1BridgeFromBinding.lean` 在给定它之后能接出 bridge，但仍要求显式
   `hq : q ≤ h`。因此它与本问题有关联，却没有证明 q-pilot/output 兼容。
2. **当前 `C1SourceBridge` membership**：要求 q-pilot 对象属于所声明的
   possible-output 集合。`C9IUTBridgeOutput.lean` 中这是显式桥接命题；它本身
   不含 `logVol = Q`，也不推出下游标量不等式，除非另证 readout 识别和 hull bound。
3. **强 C1-attain**：
   \[
   \exists D\in O,\quad \operatorname{logVol}(D)=Q.
   \]
   这是当前若把“q-pilot 是某个实际输出”写成 exact representative 时得到的
   更强目标。`C9-C1-*.md` 和 `C9-C1-APT-20261025.md` 已证明抽象 A1/A2/A3
   不足以推出它；这不是对完整 IUT 源构造的反例。
4. **论文 Cor. 3.12 / xi-f 的标量目标**：
   \[
   Q\in\{x:x\le h\},\qquad\text{即 }Q\le h.
   \]
   论文需要这个半直线成员关系，不要求先给 exact `D`。`C9-C1-FULL-TH310-
   BASIS-20261025.md` 已补回完整 Theorem 3.11 的 final evaluation / pilot
   rigidification 条款；它可能提供标量目标所需的来源，但 G1–G4（实际输出族、
   q-pilot rigidification、归一化读数、hull 上界）仍未形式化。

因此，不能用“抽象 A1/A2/A3 不蕴含 exact attainment”来宣布完整 xi-f 错误，
也不能用 xi-f 的文字把 exact representative 当成已证。

## 二、A1/A2/A3 是否是 C1 的前置

结论：**不是当前 C1 标量桥的 Lean 前置，也不应先继续扩展。**

证据如下。

- `C9A1A2A3Source.lean` 的闭合定理只对已接受的
  `Theorem311Source.Input` 边界证明 A1/A2/A3；它没有构造
  `OriginalInput → Input`，该构造也已由用户豁免。
- `C1BridgeActualSource.lean`、`C9IUTBridgeQ.lean`、`C9IUTBridgeHull.lean`
  和 `C9IUTBridgeContract.lean` 没有调用 `A1_A2_A3` 包装定理。当前
  `QHullBridge` 的真正输入是实际 q 读数、实际 source hull、hull finiteness
  和显式的 `q ≤ h`；`q ≤ h` 正是尚未证明的 C1 标量缺口。
- `C9IUTBridgeOutput.lean` 明确把 q-pilot membership 保留为单独的
  `C1SourceBridge`，没有藏进 Theorem 3.11 output，也没有把 singleton
  possible-output 当成完整 multiradial output family。
- `C9-24H-DIGEST-20261025.md` 已记录八条路线的同一结论：A1+A2+A3 的抽象
  包装不产生 q-pilot/output membership；这部分无需再重复证明。

所以 A1/A2/A3 的正确状态是：**在用户接受的 Input source boundary 上已
kernel_closed，可作为以后需要时的 proof dependency；不是开始 C1 研究的门槛。**

## 三、当前更早、更硬的兼容性阻塞：value-monoid hull

在继续追 q-pilot membership 之前，必须先检查当前 `OriginalInput` 的 hull
载体是否能承载论文所说的有限 `h`。现有生产定理给出了一个明确的分流器：

```text
SourceImageHullVolume.sourceHullVolume_eq_top_of_degreeFaithful
```

以及其无 `sorry` 包装
`C1FiniteHullObstruction.lean` 中的
`no_finite_sourceHullVolume_of_degreeFaithful`。该文件本轮复核编译通过，
`#print axioms` 只有 `propext`、`Classical.choice`、`Quot.sound`。

自然语言证明只有四步。令 `N = card(SourceVolumeIndex l) > 0`，取任意正实数
`a`，令 `s_a` 是每个分量都为 `ofAdd a` 的 constant theta-pilot point。

1. degree-faithfulness `hdeg` 给出每个分量的 log-degree 为 `a`，故 `s_a`
   属于 `sourceScalingUnits`（每个分量不等于单位）。
2. 零标签的 theta-pilot image `x₀` 在 hull 中；hull 对所有这些 scaling
   闭合，所以 `s_a*x₀` 仍在 hull。
3. 加法性给出
   \[
   \operatorname{logdeg}(s_a x_0)=N a+\operatorname{logdeg}(x_0),
   \]
   随 `a` 任意大而无界。
4. `sourceHullVolume` 是 hull 中 `ENNReal.ofReal(logdeg)` 的上确界，因而等于
   `⊤`。所以
   \[
   hdeg\;\Longrightarrow\;\neg(sourceHullVolume<\top).
   \]

这不是 C1 已被证伪；它是当前形式化载体的结构性诊断：如果用 `hdeg` 取得
paper-faithful 的 value readout，同时又要求 `QHullBridge.hullVolume_lt_top`，
两个要求在这个 hull 定义下不相容。

原因已经写在 `SourceImageHull.lean` 和
`SourceHullInterfaceDischarge.lean`：当前 value-monoid hull 对所有非单位
scalings 闭合，而论文的有限 hull 位于带有 `O_{αF_vQ}`/IQ ambient
structure 的 `λ·O` 区域。后者的 bounded unit region 不是
`OriginalInput` 的 value-monoid hull 自动给出的字段。

这也解释了为什么 `PaperP6Final.lean` 不能当 Cor. 3.12：它的
`qPilotRegion ⊆ unitRef ⊆ c6Hull` 和 Haar 单调性在 C6 surrogate 上闭合，
而既有 digest 已指出该 surrogate 的 hull 实际退化为 unit region，得到的只是
`log‖q‖ ≤ 0 ≤ 0`；尚无到 `sourceHolomorphicHull/sourceHullVolume` 的对象、
测度和归一化等价。

## 四、下一步的唯一正确顺序

**Gate 0：先解决 hull carrier compatibility。** 交付必须是以下两者之一：

### 路线 U：真实 ambient IQ/O-module 映射

从实际 source theta/evaluation 对象构造到论文 IQ carrier 的映射，证明：

- source image/hull 的像确实落在 `λ·O` 的 bounded unit region；
- Haar/log-volume 和 procession normalization 与 C9 的 `Q,h` 定义相同；
- 映射至少保持所需的一侧比较（不必先证明强 exact attainment）。

### 路线 V：受限 value carrier

若不构造 IQ 映射，就必须明确限制 scaling/degree carrier，使有限 hull 和
`hdeg` 的读数同时有意义，并重新证明 q/readout 归一化。不能继续使用当前
“全体非单位 scaling + 全实数 degree-faithfulness”的组合。

这一步完成前，所有“再补 q-pilot membership”“再算数值 gap”“再写 A1/A2/A3
包装”的路线都被剪枝：它们只能在一个已经为 `⊤` 的 hull 上工作。

**Gate 1：载体通过后，再形式化完整 Theorem 3.11 final evaluation。** 固定
以下四个最小命题，而不是直接写 `C1SourceBridge` 字段：

- G1：final evaluation 产生的真实 possible-output/rigidification family；
- G2：固定 coric/fixed q-pilot 是该 family 的一个允许 rigidification；
- G3：该 rigidification 的 readout 在同一 normalization 下等于 `Q`；
- G4：该 family 的 readout 被已修正的 ambient hull 上界 `h` 控制。

G1–G4 成立后可得到论文所需 `Q ≤ h`。只有在 G1–G3 另加 exact representative
且误差为零时，才升级报告 strong C1-attain。

## 五、数值反证/数值 gap 的位置

此前数值路线并不是没有算出真实数。记录中的 `p=12301` local Tate 实现
（`q=p^2694, qhat=pi^1347, pi^41=p`）和实际局部输出阈值是坏地方的局部对象；
它们没有组成完整 global `C`，也没有给出全部 archimedean 贡献、B-branch 和
同一 normalized target。反证 master 因而没有 source-level contradiction。
`C9-NORMALIZATION-DECISION-CORR2-20261025.md` 中的 `D_3=93.7149712746`、
`D_273=8931.1745786` 与 archimedean bound `13.1643936873` 仍是有条件的
目标尺度诊断，不是可代入 C1 的全局值。眼下不能靠挑一个数补齐缺失的源箭头；
value-monoid hull 在 degree-faithfulness 下已经是 `⊤`，必须先通过 Gate 0。

## 冻结决策

- 不再把 A1/A2/A3 设为 C1 的先决任务；现有 Input-boundary 证明保留。
- 不把 abstract non-implication 当作完整 IUT xi-f 的反例。
- 当前首要节点是 `n8-c9-hull-carrier-compatibility`；C1 q-pilot/output
  compatibility 依赖它。
- 在 carrier gate 通过前，C1、Cor. 3.12、P6 均保持 `open`，`target_accepted=false`。
