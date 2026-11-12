# Layer 0 + Layer 1 SH EAF 范围与消费者

2026-10-22。root 维护。此页把用户要求的 Layer 0 与 Layer 1 放入同一张局部 DAG；它是工作范围，不是完成声明。

## Layer 0

| 节点 | 目标 | 现有供体 | 实际消费者 | 当前状态 |
|---|---|---|---|---|
| L0.2 Tate/inverse-j | 实际 q_v/Delta/evaluator 与 Tate 参数 | TateInverseJNo1728, TateDeltaIntegral, SourceQvClosed, SourceTateParameterAlignment | L0.4 / L1 Tate 模块 | 既有 green 记录；本版未复验 |
| L0.3 G2/source quotient | 实际源覆盖范畴的有限群商 | scheme 级 affine quotient + A^G；S1/S2 陈述 | OrbicurveEtaleFundamentalGroup.galoisCategory / SourceCompletionSignQuotient | scheme 候选；源 S1 未证，L0.3 未完成 |
| L0.4 log comparison | 实际 log 方形/像/缩放/单位 | LogShell*, CompletionNorm*, log 源消费者 | L1 log-Kummer 源识别 | 部分供体；实际源比较未闭合 |
| L0.5 source Theta | AΘ、divisor、Mq→MΘ、根/deck/tempered | ThetaLinkAssembly, SourceThetaDivisor, ThetaLinkSourceSlice/candidates | L1 Theta/源 Theta 识别 | 代数装配/解析特化部分；source link 未闭合 |

## Layer 1（N8 F1–F7 源对象基础层）

| 节点 | 目标 | 现有文件/供体 | 实际消费者 | 当前状态 |
|---|---|---|---|---|
| L1-F1 equivalence | finite-etale/continuous G-set 实际等价，消 unit/counit 参数 | Example36GSetEtaleEquivalenceAssembly | Example36CurveGaloisCategory / GaloisCorrespondence | 既有文件构建记录；unit/counit/counit 自然性仍须核对当前版本 |
| L1-F2 curve pre-Galois | 实际曲线覆盖范畴的 PreGaloisCategory/G2 字段 | Example36CurveGaloisCategory, CurveEtaleCovers, CurveConnectedness | SourceOrbicurveGroupData / OrbicurveEtaleFundamentalGroup | G2 字段是 data card；未构造 inhabitant |
| L1-F3 Tate module | 任意 l≥5 的 E[l] 基数/秩/转移/全积 | Example36TateModuleProfinite, EllipticCurveSourcePiCard, TorsionAllLevels | Example36EllipticCurveAnabelioid | 部分 green；任意 l/全积边界须核对 |
| L1-F4 theta divisor | 实际 theta 级数单位/非零/除子归一化/Kummer | Example36SourceThetaDivisor, ThetaSeries, GaussianKernel | SourceThetaGenerator / Theta-link | 部分解析特化；除子/Kummer/线丛未闭合 |
| L1-F5 log-Kummer | principal-unit log 相容、scaled/unscaled、perfection | Example36SourceLogKummerIdentification, SourcePerfection, LogDomainActual | SourceTheaterCarrier / VerticalLogKummer | 部分 green；自然性与实际源识别未闭合 |
| L1-F6 Gaussian arithmetic | 整数环、(2+i) 剩余域、完成度运输 | Example36GaussianIntegralBasis, GaussianSplitPlaceArithmetic | concreteGaussianFivePlace / 源值群 | 部分 green；单位群 v=1 与 chosen place 计算规则仍缺 |
| L1-F7 Tate uniformization | 曲线/theta 变换律、点映射、群律 | Example36TateUniformization, TateGroupLaw, TatePoint* | L1 源 Tate/q 输入 | 条件性；点映射/解析均匀化未闭合 |
| L1-F8 Theta-link cover/slice | AΘ cover、slice/积函子、源覆盖比较 | ThetaLinkAssembly, ThetaLinkSourceCover/Slice candidates | L0.5 source Theta | 代数装配 green；几何覆盖未闭合 |

## 调度规则

- 每个文件唯一 owner；同一文件不得两人写。
- 每包先固定：对象、量词、假设、consumer、供体版本、阶段、验收出口。
- 阶段 2 允许具名 sorry 的 statement_compiles；阶段 3 才要求 proof_body_checked/kernel_closed。
- 不把旧 green 记录、Project import、文件数当成本版完成。
- 每个 track 的下一包由 root 从 queue 取；独立文件可并行，共享接口先冻结。

## 当前优先级

1. L0.3 S1 comparison statement/proof（已被 stage1 记录定位为源 G2 必需桥）。
2. L1-F2 curve PreGalois 的 G2 字段；与 S1/S2 共用消费者。
3. L1-F1 equivalence 当前版本复验；它是 F2 的范畴基础。
4. L0.4/L1-F5 log 与 L0.5/L1-F4/F8 Theta 作为独立 track 并行，但不得绕过实际源对象比较。

## 阶段观修正（2026-10-22）

不存在全局 stage1/2/3 屏障。每个节点独立进入阶段；阶段 3 证明中产生的新对象/比较递归登记为子节点。详见 [FRACTAL-STAGES.md](FRACTAL-STAGES.md)。调度只按节点就绪、文件冲突和 consumer 判断。
