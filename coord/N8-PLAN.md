# N8 全量闭环计划（2026-10-22）

用户要求：先把 N8 全部按 SHEAF 方法过一遍，允许大量具名 sorry，先闭环 N8；然后再重点搞下面层。此页是 N8 的范围/阶段/consumer 总表，不宣称数学闭合。

## 六组（用户层号）

| 组 | 对应 distilled | 目标 | 实际 consumer | 当前状态 |
|---|---|---|---|---|
| 1 | 01 | 实际 prime-strip/Frobenioid/Hodge theater/source objects | SourceOriginalInput / SourceTheorem311Assembly | 有大量底座与 data card；真实 theater/link 识别 open |
| 2 | 03 | 竖直 log-Kummer + K1/K2 源实现与下降 | SourceK1K2Construction / SourceTheorem311 | 局部 log/shell 件多；源侧 K1/K2 未闭合 |
| 3 | 02 | q/theta-pilot -> 算术 tensor 区域、生成元落点 | ArithmeticTensorTupleBlock / N5 / Theorem311 | q-side 最小切片与 ArithmeticQPilot 候选；源映射 open |
| 4 | 04 | Thm3.11 多径向输出 + Ind1–Ind3 | SourceTheorem311Assembly / SourceFiniteMultiradial | 有抽象商/轨道/upper-semi/有限实例；实际输出 open |
| 5 | 05 | IPL/SHE/APT 跨列运输 | Theorem311 / Cor312 Step(xi) | 只有接口/通用复合；实际五项 open |
| 6 | 06 | hull + 算术 degree = 归一化 log-volume + Ob3-3/qSigned | Cor312ToABCBridgeInterface / ABC | hull/紧性/Haar/加权公式有骨架；实际比较 open |

## N8 闭环的定义（本阶段）

- 六个组各自有 stage1 记录：精确 paper objects、量词、consumer、Lean donors、gaps、最小 stage2 statement。
- 六个组各自有 stage2 statement（能精确者；不能精确者明确标 stage1 open，不能造假）。
- 所有已写 statement 允许具名 sorry，但类型必须引用真实定义；不得把待证结论塞进自由字段。
- 组间依赖显式记录；不得把同一卡/同一数据的多个字段当成多个独立证明。
- N8 “闭环”在此先指 **结构闭合/依赖图闭合**，不是 kernel 闭合；kernel/axiom/target_accepted 另列。

## 依赖顺序

    1 source objects
    -> 2 log-Kummer/K1K2 and 3 q/theta-pilot
    -> 4 Thm3.11 multiradial
    -> 5 IPL/SHE/APT
    -> 6 hull/degree/log-volume
    -> 3.12 -> ABC

但按 fractal-stage 规则，独立子节点可并行；组间共享接口先冻结。

## 当前执行

- 6 个 subagent 正在写各组 groupN-STAGE1.md。
- 8 个 durable teammate 继续手头 stage2/3：
  - kummer scheme G2
  - primespine F2 consumer
  - ipl donor axiom probe
  - qside F8d/F8 consumer
  - vol F3.a proof
  - multiradial F4 production integration
  - logdescent F5.a
  - transport L0.4 principal log square
- 收到 6 份 stage1 后，root 统一登记 DAG 节点，并按组排 stage2 statement；允许大量 sorry。

## 验收边界

- named sorry 只表示 statement_compiles，不表示 proof_body_checked。
- 每个 stage2 文件必须记录：目标类型、变量/量词/假设、依赖版本、consumer、尚未证明的精确缺口。
- 不把旧 Project import、文件数、card inhabitant 当 N8 闭合。

## Sorry 规则（用户 2026-10-22 纠正）

见 [SORRY-POLICY.md](SORRY-POLICY.md) 和 [SORRY-REGISTRY.md](SORRY-REGISTRY.md)。

- 只允许定理级、精确类型、有来源/consumer/NL proof/exact gap 的 named sorry。
- 禁止用 noncomputable def ... := by sorry 制造 source objects/data。
- 缺对象时用 obligation structure + 显式参数，不用假对象。
- 条件必须是 paper 原输入或已证接口；新增假设不算闭合。
- statement_compiles 不等于 proof_body_checked，更不等于 N8 完成。

## 2026-10-22 stage1 closure

六组 stage1 均已交付；N8 stage1 结构闭合达成。当前进入六组 stage2 statement/证明：Group1Statement、LogDescentStatement、group3-S1、group4/Statements、Group5Statements、Group6Normalization。stage1 closure 不是数学闭环。


## 2026-10-22 最新执行路线：按 N8 总出口闭合

用户要求以闭合为目标，不再停留在各组小引理或A/B选项。执行路线见 [N8-CLOSURE-ROUTE.md](N8-CLOSURE-ROUTE.md)。

本轮新路线取代“六组各交一个最小statement即进入收尾”的执行顺序：C0冻结原文总目标，C1–C9围绕同一实际源输入构造对象、见证输出、算法相容、真实hull、归一化/degree和q的实现或逼近，C10实际调用整链。先验收整体statement/dependency closure，再消去具名证明义务，最终验收N8数学闭合。旧六组小结果作为供体复用，不以其状态代替父目标状态。

group5采用实际源算法双侧解释，不预设整个Strip/Output等价；group6采用IV1.4(i)/Remark1.7.1的局部归一化及权重。最终必须消掉`hq`，不能让自由qSigned或thetaSigned=0代替原文数值。本条为路线更新，不是数学完成或新agent派发记录。
