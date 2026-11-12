# Fractal per-node stages

2026-10-22. 用户指出：阶段 3 是分形的，不存在一个全局时间点让整个项目统一进入某一阶段。此页落实这一点；不修改 Lean 源码。

## 规则

- 每个 DAG 节点独立维护 stage 1 / stage 2 / stage 3；同一时刻不同节点可以处于不同阶段。
- 阶段 1 可在任何阶段 3 证明中递归产生子节点：证明某定理时发现新对象/比较/前置，就新建子节点，先固定对象、consumer、自然语言证明和缺口。
- 阶段 2 的具名 sorry 是节点局部接口，不是全局进度闸门；父节点可在子节点仍 stage 2 时尝试 stage 3，但父节点保持未闭合。
- 阶段 3 成功只把该节点置 proof_body_checked；不会自动把兄弟节点或父节点推进到下一阶段。
- 不存在“全 Layer0 先 stage1，再全 Layer1 stage2”的全局屏障。调度只看节点是否就绪、文件是否冲突、consumer 是否明确。
- 每包结束只更新本节点阶段、子节点、consumer 和下一步，不改写其他节点的阶段。

## 节点阶段记录模板

    node:
    stage1: open/complete; source, consumer, natural-language proof, gaps
    stage2: not_started/statement_compiles; file, declaration, named sorry
    stage3: open/proof_body_checked/kernel_closed; dependencies, build/axiom evidence
    children: new nodes spawned by stage3 gaps
    ready_action: one concrete next step

## 当前节点阶段（局部快照）

| node | stage1 | stage2 | stage3 | children / next |
|---|---|---|---|---|
| l03-s1-scheme-orbicurve-comparison | partial: consumer 和 proof deps 已列，representability/equivalence 缺口未闭合 | statement_compiles | open | 子节点：stack representability、scheme/stack finite-etale predicate、cover equivalence、fiber comparison |
| l03-s2-hascolimits-transport | complete | statement_compiles/proof body | proof_body_checked；kernel audit 未跑 | 子节点：axiom probe |
| l03-source-g2-statement | partial | statement_compiles | open | 子节点：完整 PreGaloisCategory 其他字段、fiber functor、IsFundamentalGroup |
| l1-f2-scheme-g2 | partial | statement_compiles | open；依赖 kummer scheme G2 | 子节点：scheme HasColimits 定理 |
| l1-f6-gaussian | complete | rational-unit lemma 待写 | open | 子节点：v=1 单位群 packaging |
| l1-f8-theta-cover | complete consumer record | consumer statement 待写 | open | 子节点：source ATheta/slice binding |
| l1-f1-equivalence | stage1 running | — | — | 先固定 unit/counit 缺口 |
| l1-f3-tate-module | stage1 running | — | — | 先固定任意 l/全积字段 |
| l1-f4-theta-divisor | stage1 running | — | — | 先固定除子/Kummer 缺口 |
| l1-f5-log-kummer | stage1 running | — | — | 先固定自然性/缩放缺口 |

## 调度含义

- 当前可立即做 stage3 的节点：S2（已 proof_body_checked，只差 axiom probe）、F6 的 rational-unit 引理、kummer 的 scheme HasColimits。
- 当前只能做 stage1/2 的节点：S1 子结构、F1/F3/F4/F5、F8 source binding。
- 不得因为 F1/F3/F4/F5 还在 stage1 就阻塞 S2/F6 的 stage3；也不得因为 S2/F6 stage3 绿色就宣称 Layer1 完成。

## 2026-10-22 追加局部节点

| node | stage1 | stage2 | stage3 |
|---|---|---|---|
| l03-s2-hascolimits-transport | complete | statement_compiles | kernel_closed（axiom probe 标准三公理；probe 为逐字副本） |
| l1-f2-scheme-g2 | complete | statement_compiles | open；等 kummer scheme HasColimits |
| l1-f4 | complete | next declaration fixed | F4.a stage3 进行；F4.b blocked by a |
| l1-f5 | complete | F5-a fixed | F5-a stage3 进行 |
| l1-f6 | complete | rational-unit fixed | stage3 进行 |
| l1-f8 | complete | consumer statement written, blocked by red donor | source-binding child stage1 进行；donor 修复由 ipl 负责 |
| l1-f3 | complete | elliptic torsion card statement 待写 | open |
| l1-f1 | stage1 进行 | — | — |

## Subagent 与 durable teammate 的分工（2026-10-22 用户确认）

- **stage 1 可以大量派给 subagent**：范围核对、consumer 定位、文件/声明盘点、精确缺口、写 stage1 记录。输出必须是带路径、SHA、对象/量词、consumer 和下一 statement 的完整记录。
- **stage 2/3 默认交给 durable teammate**：需要跨轮记忆、文件所有权、接口演化、依赖更新和反复编译反馈；subagent 上下文短，不适合承担长期证明主线。
- 可交给 subagent 的 stage 2/3 例外：单个文件、单一精确声明、已有完整公共供体、无需跨轮记忆、可在一次 bounded 任务内编译验收。
- subagent 的 stage1 记录是 teammate 接手的唯一接口；teammate 不应要求 subagent 记忆历史。
- teammate 名额仍为 8；subagent 是 stage1 扩容和 bounded lemma 的补充，不是替代长期 owner。
