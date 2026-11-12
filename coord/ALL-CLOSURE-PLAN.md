# 全部闭合执行计划（SHEAF，named-sorry closure）

日期 2026-10-24。用户指令：全部闭合，先易后难，多线程，复用已有结论，不追求 no-sorry。

## 闭合标准

一个节点在本计划中算“闭合”当且仅当：
1. 有编译通过的精确 Lean 目标陈述（statement_compiles），或已有可复用 target；
2. 缺口语义可见，并以 theorem-level named sorry 登记；
3. 没有 free field / True / 任意 Set 冒充源对象；
4. 实际 consumer 由 C10/上层 theorem 调用；
5. 状态明确标为 named-sorry closure，不标 target_accepted/math closed。

新 sorry 是预期产物，不是失败。禁止为了 no-sorry 缩目标或造假。

## Wave 1（并行，当前）

| owner | 文件 | 目标 |
|---|---|---|
| primespine | ProjectClosureManifest.md + ABCNamedClosure.lean | 全节点盘点 + Cor312/ABC named closure |
| qside | L02L04NamedClosure.lean | L0.2 local field/Tate + L0.4 log comparison |
| logdescent | L05C2NamedClosure.lean | L0.5 source Theta + C2 完整 target |
| kummer | C3T11NamedClosure.lean | C3 源对象 + T11 q identification |
| iplsheapt | C5L1F7NamedClosure.lean | C5 完整 + L1-F7 Tate uniformization |
| volumedet | C6C7C8NamedClosure.lean | C6/C7/C8 named closure |
| transport | C9QThetaValuesNamed.lean | C9 Q/Theta/Values |
| multiradial | C9P6Closure.lean | P6 双构造装配 |

## Wave 2

- C9 P0-P7 剩余 source-object 细化；P6 exact/epsilon 的源构造。
- 3.11 source assembly 与 3.12 hull/volume target。
- 复用 C9-TARGET-V3、P6 组件、C1/C2/C3/C5/C6/C7/C8 actual 结果。

## Route guard (2026-10-24, user correction)

- 旧 Layer0/Layer1/ABC 节点不一定仍与当前 N8 线路一致；不得自动按旧 DAG 闭合。
- 旧 layer 只作 donor/证据库，只有当前 N8 P6 线路实际消费者需要时才复用。
- ABC/Cor312 暂缓，不能当 N8 闭合；待 N8 route manifest 明确后再决定。
- Wave1 旧 layer closure 任务已撤销，改为 P6Bridge/P6LClosure/P6SHEIndClosure/N8RouteClosure。
- 若旧节点与当前 source route 冲突，标 off-route，不进入 closure target。

## Wave 3

- Layer0/Layer1 open 节点：l03-g2、l1-f1、l1-f7 等。
- Cor312ToABCBridge 实际 construction（named gap）。
- ABC 最终 target 的 conditional closure。

## 复用清单（不重造）

- C1: NativeC1 place/index/bad place/tower laws
- C2: NativeLogSlice/local log shell
- C3: nativeQActual/roots/KummerClass/P6Tensor
- C5: SHERepresentationActual/C5SHEIntegration/APT no-go
- C6: C6ActualIdentification.actual_isActual
- C7: source U containment/Haar/C7UToIQProof
- C8: actual arithmetic profile/C8DegreeActual
- C9: C9QPilotRegion/P6ChainA/P6L/P6Hull/P6Comparison
- T11: T11Reductions q-identification reduction
- C10: N8ClosureFull named-sorry closure

## 当前已知 boundaries

- 所有 closure 仍是 named-sorry，不是零 sorry 数学闭合。
- 简化对象按 OBJECT-SIMPLIFICATION-AUDIT 标注。
- L、alpha、R_alpha、global L、Theta/Values 的完整源构造仍是 open。

## Binding guard (2026-10-24)

Legacy C10 closure (`N8ClosureFull`) and old Layer0/Layer1 closures MUST NOT be reported or consumed as paper N8 closure. See `coord/CLOSURE-GUARD.md`. Only C9-TARGET-V3/P6 target acceptance may be called paper N8 closure.

## Wave 2 (2026-10-24, dispatched)

- multiradial: C9PaperClosure.lean (Q/Theta/Values + comparison)
- primespine: PaperN8Closure.lean (paper N8 target, not legacy)
- logdescent: P6LActual.lean (global readout actual attempt)
- volumedet: P6HullActual.lean (hull setup actual attempt)
- qside: P6BridgeActual.lean (native bridge actual attempt)
- kummer: P6TensorActual.lean (tensor landing actual/no-go)
- iplsheapt: P6APTActual.lean (APT/permitted actual/no-go)
- transport: C7C8ActualAttempt.lean (U2IQ/Ob3-3 attempt)

Wave1 all 8 central compile exit0. No paper N8 closure yet.
